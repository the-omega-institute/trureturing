# Pinned real algebraic source: TauCeti.Topology.LocallyConstant.Preconnected.

## Abstract

Pinned real algebraic source: TauCeti.Topology.LocallyConstant.Preconnected.

This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Topology/LocallyConstant/Preconnected.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.

A locally constant function on a preconnected domain is constant on that domain. If it agrees eventually with a value at a point of the domain, the neighborhood is inhabited and supplies the comparison point; the pinned preconnected constancy theorem then gives the value everywhere. The function may have arbitrary codomain, and the original point/domain membership and local constancy conditions are retained. This also directly supplies the anonymous example through the same theorem, without a separate retained statement.
