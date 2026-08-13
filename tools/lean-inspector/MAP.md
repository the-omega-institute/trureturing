# Lean Inspector Map

- `Inspector.lean` is the sole Lean producer for canonical raw module data.
- `inspect.sh` prepares the pinned Lean environment, preserves complete phase logs,
  invokes the producer, and emits a SHA-256 sidecar for artifact handoff.

The report contains source-bound module, import, declaration, axiom, and structural
statement material. Statement IDs remain owned by the .NET canonical statement writer.
