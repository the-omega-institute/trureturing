# Buffered Whole-Path Retained-Cone Extension

For compact Hausdorff `X` and a finite-cover shadowing map `f`, fix finite
old and new discrete alphabets.  The old closed buffers satisfy
`K(a) ⊆ interior(P(a)) ⊆ P(a) ⊆ interior(C(a))`; the new buffers satisfy
`L(b) ⊆ interior(D(b))`, and the inner interiors cover `X`.

The theorem `D5/S1/Dynamics/Shadowing/BufferedConeExtension`
`buffered_whole_path_extension` is the finite retained-cone step.  Given a
finite old labelled graph whose every old whole word has one `P`-orbit
realizer and which contains every `K`-orbit name, it chooses a finite
shadowing-control cover and builds vertices `V × T × B`.  An edge carries one
actual point `t : X` witnessing the old `P` and new `L` constraints at both
ends, as well as the old edge.  The first-coordinate projection preserves
edges and lifts every specified infinite old vertex path, including time zero.

Every complete new graph path is traced by one orbit in the outer `C` and `D`
interiors at every time.  Every specified point `x` and every complete
old-`K`/new-`L` name is in the new complete graph language.  The construction
does not assume that `f` is onto and permits empty source or graph cases via
the displayed hypotheses.  It is a finite theorem for one fixed old cone;
it does not choose the global uniform follower bounds needed for Peng's full
Question 5.1, and the original unrestricted question remains unresolved.

The transfer cover is obtained by compactness from the finite family of open
sets that separate each closed source set from its outer interior.  The
shadowing contract is the existing finite-open-cover `HasShadowing`; no new
tracing axiom is introduced.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/BufferedConeExtension.buffered_whole_path_extension`
- Dependency: [FiniteObservationSofic](FiniteObservationSofic.md)
- Dependency: [MittagLefflerInverseLimit](MittagLefflerInverseLimit.md)
- Literature context: `Library/Dynamics/peng2026shadowing.md`
