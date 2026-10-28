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
    // buffer argumen yang diisi fungsi baca (arg ke-1)
    exists(FunctionCall fc |
      fc.getTarget().hasGlobalName(["recv", "recvfrom", "read", "fread"]) and
      source.asDefiningArgument() = fc.getArgument(1)
    )
    or
    // wrapper osdep: wi_read(wi, ..., buf, len, ri) -> cari berdasarkan nama
    exists(FunctionCall fc |
      fc.getTarget().getName().regexpMatch("(wi_read|.*_read_packet|.*_read)") and
      fc.getTarget().getFile().getRelativePath().matches("lib/osdep/%") and
      source.asDefiningArgument() = fc.getAnArgument()
    )
    or
    // wi_read lewat pointer fungsi (indirect call)
    exists(ExprCall ec |
      source.asDefiningArgument() = ec.getAnArgument() and
      ec.getExpr().(PointerFieldAccess).getTarget().getName() = "wi_read"
    )
    or
    // pcap: pointer hasil dari pcap_next / pcap_next_ex (arg ke-2 adalah const u_char **)
    exists(FunctionCall fc |
      fc.getTarget().hasGlobalName("pcap_next") and
      source.asExpr() = fc
    )
    or
    exists(FunctionCall fc |
      fc.getTarget().hasGlobalName("pcap_next_ex") and
      source.asDefiningArgument() = fc.getArgument(2)
    )
  }

  predicate isSink(DataFlow::Node sink) {
    exists(FunctionCall fc |
      fc.getTarget().hasGlobalName(["memcpy", "memmove"]) and
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
