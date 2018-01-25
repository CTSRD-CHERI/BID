// C function wrappers
// get system time
import "BDPI" function Bit#(64) sysTime ();

////////////////////////
// logging primitives //
////////////////////////

typeclass PrintLog#(type a);
  function Action printLog(a msg);
  function Action printTLog(a msg);
  function Action printLogPlusArgs(String arg, a msg);
  function Action printTLogPlusArgs(String arg, a msg);
  function Action printPlusArgs(String arg, a msg);
  function Action printTPlusArgs(String arg, a msg);
endtypeclass

// Fmt instance
instance PrintLog#(Fmt);

  function Action printLog(Fmt msg) = action
    `ifndef NO_LOGS
      $display(msg);
    `endif
  endaction;
  function Action printTLog(Fmt msg) = action
    `ifndef NO_LOGS
      $display("time %0t -- ", $time, msg);
    `endif
  endaction;
  function Action printLogPlusArgs(String parg, Fmt msg) = action
    `ifndef NO_LOGS
      printPlusArgs(parg, msg);
    `endif
  endaction;
  function Action printTLogPlusArgs(String parg, Fmt msg) = action
    `ifndef NO_LOGS
      printTPlusArgs(parg, msg);
    `endif
  endaction;
  function Action printPlusArgs(String parg, Fmt msg) = action
    Bool doPrint <- $test$plusargs(parg);
    if (doPrint) $display(msg);
  endaction;
  function Action printTPlusArgs(String parg, Fmt msg) = action
    Bool doPrint <- $test$plusargs(parg);
    if (doPrint) $display("time %0t -- ", $time, msg);
  endaction;

endinstance

// String instance
instance PrintLog#(String);

  function Action printLog(String msg) = action
    `ifndef NO_LOGS
      $display(msg);
    `endif
  endaction;
  function Action printTLog(String msg) = action
    `ifndef NO_LOGS
      $display("time %0t -- ", $time, msg);
    `endif
  endaction;
  function Action printLogPlusArgs(String parg, String msg) = action
    `ifndef NO_LOGS
      printPlusArgs(parg, msg);
    `endif
  endaction;
  function Action printTLogPlusArgs(String parg, String msg) = action
    `ifndef NO_LOGS
      printTPlusArgs(parg, msg);
    `endif
  endaction;
  function Action printPlusArgs(String parg, String msg) = action
    Bool doPrint <- $test$plusargs(parg);
    if (doPrint) $display(msg);
  endaction;
  function Action printTPlusArgs(String parg, String msg) = action
    Bool doPrint <- $test$plusargs(parg);
    if (doPrint) $display("time %0t -- ", $time, msg);
  endaction;

endinstance
