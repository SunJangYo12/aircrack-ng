/**
 * @name Data jaringan ke ukuran memcpy
 * @kind path-problem
 * @problem.severity error
 * @id custom/net-to-memcpy-size
 */
import cpp
import semmle.code.cpp.dataflow.new.TaintTracking

module NetConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) {
    // buffer yang diisi oleh recv/read
    exists(FunctionCall fc |
      fc.getTarget().hasGlobalName(["recv", "recvfrom", "read"]) and
      source.asDefiningArgument() = fc.getArgument(1)
    )
    or
    // pointer yang dikembalikan pcap_next
    exists(FunctionCall fc |
      fc.getTarget().hasGlobalName("pcap_next") and
      source.asExpr() = fc
    )
  }

  predicate isSink(DataFlow::Node sink) {
    exists(FunctionCall fc |
      fc.getTarget().hasGlobalName("memcpy") and
      sink.asExpr() = fc.getArgument(2)
    )
  }
}

module NetFlow = TaintTracking::Global<NetConfig>;
import NetFlow::PathGraph

from NetFlow::PathNode source, NetFlow::PathNode sink
where NetFlow::flowPath(source, sink)
select sink.getNode(), source, sink,
  "Ukuran memcpy berasal dari $@.", source.getNode(), "data jaringan"

