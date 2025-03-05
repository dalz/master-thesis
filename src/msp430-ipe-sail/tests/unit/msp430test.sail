$include "testStatusbits.sail"
$include "testRegister.sail"
$include "../../_compilation/tests/unit/test-ipe.sail"

function main() : unit -> unit = {
  testStatusbits();
  testRegister();
  test_ipe();
  print_endline("Success");
}