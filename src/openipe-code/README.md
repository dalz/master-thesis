In a few days/weeks, I will upload the code to <https://github.com/martonbognar/openipe>, but for now I'll paste the most important files here.

- `bootcode.s43`: this is our implementation of TI's bootcode, that sets up the IPE registers according to the configuration struct in memory.
- `tests/*`: these are (a subset of) the unit tests we've written to test the bootcode and the hardware's behavior. In all cases, you should assume that the code in `*.s43` runs after the bootcode. The `*.v` files contain Verilog stimuli that drive the tests and check whether they succeed by checking certain hardware signals. Of course, if you want to use these tests, you'll have to convert these conditions into some other form.
