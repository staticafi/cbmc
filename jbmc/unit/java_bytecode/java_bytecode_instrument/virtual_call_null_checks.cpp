/*******************************************************************\

Module: Unit test to check Java virtual calls via a pointer
        yield a correct sequence of not-null assumptions.

Author: Diffblue Limited.

\*******************************************************************/

#include <java-testing-utils/load_java_class.h>

#include <util/expr_iterator.h>

#include <analyses/local_safe_pointers.h>
#include <ansi-c/goto-conversion/goto_convert_functions.h>
#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

// We're expecting a call "something->field . B.virtualmethod()":
static bool is_expected_virtualmethod_call(
  const goto_programt::instructiont &instruction)
{
  if(instruction.type() != FUNCTION_CALL)
    return false;
  const auto &called_function = instruction.call_function();
  if(!can_cast_expr<class_method_descriptor_exprt>(called_function))
    return false;
  if(called_function.get(ID_identifier) != "java::B.virtualmethod:()V")
    return false;
  if(instruction.call_arguments().size() != 1)
    return false;
  const auto &this_argument = instruction.call_arguments()[0];
  if(this_argument.id() != ID_member)
    return false;
  if(to_member_expr(this_argument).compound().id() != ID_dereference)
    return false;

  return true;
}

SCENARIO(
  "java_bytecode_virtual_call_null_checks",
  "[core][java_bytecode][java_bytecode_instrument]")
{
  GIVEN("A class that makes a virtual call via a pointer")
  {
    symbol_tablet symbol_table = load_java_class(
      "VirtualCallNullChecks", "./java_bytecode/java_bytecode_instrument");

    WHEN("The virtual call is converted")
    {
      namespacet ns(symbol_table);
      goto_functionst goto_functions;
      goto_convert(symbol_table, goto_functions, null_message_handler);

      const auto &main_function =
        goto_functions.function_map.at("java::VirtualCallNullChecks.main:()V");

      THEN("The loaded function should call B.virtualmethod via a pointer")
      {
        // This just checks that the class actually makes the expected call,
        // i.e. that it hasn't been optimised away or similar.
        std::size_t found_virtualmethod_calls =
          std::count_if(
            main_function.body.instructions.begin(),
            main_function.body.instructions.end(),
            is_expected_virtualmethod_call);

        REQUIRE(found_virtualmethod_calls == 1);
      }
      THEN("All pointer usages should be safe")
      {
        // This analysis checks that any usage of a pointer is preceded by an
        // assumption that it is non-null
        // (e.g. assume(x != nullptr); y = x->...)
        local_safe_pointerst safe_pointers;
        safe_pointers(main_function.body);

        for(auto instrit = main_function.body.instructions.begin(),
              instrend = main_function.body.instructions.end();
            instrit != instrend; ++instrit)
        {
          for(auto it = instrit->code().depth_begin(),
                   itend = instrit->code().depth_end();
              it != itend;
              ++it)
          {
            if(it->id() == ID_dereference)
            {
              const auto &deref = to_dereference_expr(*it);
              REQUIRE(
                safe_pointers.is_safe_dereference(deref, instrit));
            }
          }

          if(instrit->has_condition())
          {
            const auto &condition = instrit->condition();

            for(auto it = condition.depth_begin(),
                     itend = condition.depth_end();
                it != itend;
                ++it)
            {
              if(it->id() == ID_dereference)
              {
                const auto &deref = to_dereference_expr(*it);
                REQUIRE(safe_pointers.is_safe_dereference(deref, instrit));
              }
            }
          }
        }
      }
    }
  }
}
