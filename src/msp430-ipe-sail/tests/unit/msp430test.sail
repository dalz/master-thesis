$include "testStatusbits.sail"
$include "testRegister.sail"
$include "test-ipe.sail"

function main() : unit -> unit = {
  testStatusbits();
  testRegister();
  test_ipe();
  print_endline("Success");
}