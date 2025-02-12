$include "testStatusbits.sail"
$include "testRegister.sail"

function main() : unit -> unit = {
  testStatusbits();
  testRegister();
   print_endline("Success");
}