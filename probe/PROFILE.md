# Lean probe verification and cost

Source SHA-256: 6446e075b2ffb898fa8be5577fd50e2f0ede2ee83099bd28f0149a58bc02deba

Toolchain: leanprover/lean4:v4.33.0. Both invocations exited 0 with no warnings. Both used the brief's exact PATH and the previously cache-stamped worktree.

Primary cost command:

```sh
export PATH="$HOME/.dotnet:$HOME/.elan/bin:$HOME/.cargo/bin:/usr/local/share/dotnet:/opt/homebrew/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin"
/usr/bin/time -l lake env lean -Dprofiler=true -Dtrace.profiler=true -Dtrace.profiler.threshold=1000 probe/AyadProbe.lean
```

```text
import took 4.36s
'AyadProbe.property_coprime' depends on axioms: [propext, Classical.choice, Quot.sound]
'AyadProbe.sparse_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'AyadProbe.witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'AyadProbe.result' depends on axioms: [propext, Classical.choice, Quot.sound]
cumulative profiling times:
	attribute application 0.0537ms
	blocked (unaccounted) 184ms
	compilation (IR) 0.268ms
	compilation (LCNF base) 3.42ms
	compilation (LCNF impure) 1.66ms
	compilation (LCNF mono) 1.91ms
	congr simp thm 1.22ms
	dsimp 0.519ms
	elaboration 39.4ms
	fix level params 0.461ms
	import 4.36s
	initialization 13.8ms
	instantiate metavars 1.92ms
	interpretation 424ms
	let-to-have transformation 0.252ms
	linting 12.4ms
	module linting 0.000958ms
	norm_num 4.43ms
	overlappingInstancesLinter 4.19ms
	parsing 4.26ms
	process pre-definitions 7.8ms
	ring 24.7ms
	share common exprs 5.38ms
	simp 74.9ms
	tactic execution 119ms
	tacticAnalysis 14.2ms
	type checking 74.8ms
	typeclass inference 123ms
        8.60 real         1.43 user         2.03 sys
          1730183168  maximum resident set size
                   0  average shared memory size
                   0  average unshared data size
                   0  average unshared stack size
              189246  page reclaims
               81750  page faults
                   0  swaps
                   0  block input operations
                   0  block output operations
                   0  messages sent
                   0  messages received
                   0  signals received
               25926  voluntary context switches
               73801  involuntary context switches
         12848019595  instructions retired
          4848192966  cycles elapsed
          1074799152  peak memory footprint

```

The pinned Lean profiler calls the kernel addition phase `type checking`, not `checked`: `Lean/AddDecl.lean:184` wraps `Environment.addDeclAux` in that timer. The primary run therefore measures kernel checking at 0.0748 seconds. Wall time includes Lake and imports; the primary import phase was 4.36 seconds.

An instrumented diagnostic run of the same source with threshold 0 also exited 0: wall 22.34 seconds, cumulative kernel `type checking` 0.0998 seconds, peak RSS 1997275136 bytes. Threshold 0 emits detailed tracing; this run is not used as the normal wall-cost reading. Its relevant declaration measurements are:

```text
[Kernel] [0.001612] ✅️ typechecking declarations [AyadProbe.property_coprime]
[Kernel] [0.009205] ✅️ typechecking declarations [AyadProbe.sparse_spec]
[Kernel] [0.003856] ✅️ typechecking declarations [AyadProbe.witness]
[Kernel] [0.004238] ✅️ typechecking declarations [AyadProbe.result]
```

The recursive sparse list is a symbolic construction. Its checked specification takes 0.009205 seconds in the instrumented run; it does not instantiate or enumerate large lists in the proof term. Both the exact witness and the complete result have only propext, Classical.choice, and Quot.sound in their axiom closure. No sorryAx occurs.
