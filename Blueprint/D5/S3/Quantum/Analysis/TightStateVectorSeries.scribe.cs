using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class TightStateVectorSeriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-rank tightness of a positive normalized functional on bounded Hilbert-space operators gives one countable vector family representing every bounded operator.",
        H("Tight State Vector Series"),
        Blocks(Describe.Lean(
            DescribeId.Create("positive-functional-vector-series-of-finite-rank-tightness"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/TightStateVectorSeries.positive_functional_vector_series_of_finite_rank_tightness"),
            H("A single vector family for the whole positive functional"),
            StatementSource.FromAuthor(Disp(Seq(
                Forall, Sp, F.Id("H"), Sp, InMacro, Sp, Call("ComplexHilbertSpaces"), Comma, Esc,
                Forall, Sp, Phi, Sp, InMacro, Sp,
                    Call("PositiveComplexLinearMaps", Call("BoundedOperators", F.Id("H")),
                        Seq(Mathbb, Grp(F.Id("C")))), Comma, Esc,
                Forall, Sp, F.Id("E"), Sp, InMacro, Sp,
                    Call("Sequences", Call("BoundedOperators", F.Id("H"))), Comma, Esc,
                Open,
                    Call("Apply", Phi, D(1)), Sp, Eq, Sp, D(1), Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("j"), Sp, InMacro, Sp,
                        Mathbb, Grp(F.Id("N")), Comma, Esc,
                        Call("IsStarProjection", Call("E", F.Id("j"))), Sp, Land, Sp,
                        Call("FiniteDimensional", Seq(Mathbb, Grp(F.Id("C"))),
                            Call("Range", Call("E", F.Id("j")))), Close, Sp, Land, Sp,
                    Call("Tendsto", Seq(F.Id("j"), Sp, Mapsto, Sp,
                        Call("RealPart", Call("Apply", Phi,
                            Seq(D(1), Minus, Call("E", F.Id("j")))))),
                        Call("AtTopNat"), Call("Neighbourhood", D(0))),
                Close, Sp, Implies, Sp,
                Exists, Sp, F.Id("u"), Sp, InMacro, Sp,
                    Call("Sequences", F.Id("H")), Comma, Esc,
                Call("HasSum", Seq(F.Id("k"), Sp, Mapsto, Sp,
                    Call("NormSquared", Call("u", F.Id("k")))), D(1)), Sp, Land, Sp,
                Open, Forall, Sp, F.Id("S"), Sp, InMacro, Sp,
                    Call("BoundedOperators", F.Id("H")), Comma, Esc,
                    Call("HasSum", Seq(F.Id("k"), Sp, Mapsto, Sp,
                        Call("Inner", Call("u", F.Id("k")),
                            Call("S", Call("u", F.Id("k"))))),
                        Call("Apply", Phi, F.Id("S"))), Close))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("ComplexHilbertSpaces means arbitrary types with a normed additive commutative group, a complex inner-product space structure, and completeness. BoundedOperators(H) is the actual space H ->L[C] H, with identity 1 and operator composition. PositiveComplexLinearMaps comprises complex linear maps preserving the positive order; continuity is derived in the proof. Sequences(X) means functions from the natural numbers to X. IsStarProjection means self-adjointness and idempotence of the actual operator, and Range is its actual linear range.")),
                Paragraph(Text("The quantifiers range over every such H, every positive complex linear map phi, and every sequence E of bounded operators. The hypotheses are phi(1)=1, finite-dimensional complex range and star-projection structure for each E(j), and Tendsto of j maps to Re(phi(1-E(j))) along natural-number atTop to the neighbourhood of real zero. No monotonicity or commutation of the projections is required.")),
                Paragraph(Text("HasSum uses the net of sums over all finite subsets of the natural numbers. NormSquared(x) is the real value ||x||^2; Inner(x,y) is the complex inner product, conjugate-linear in x and linear in y. A single family u has HasSum(k maps to ||u(k)||^2,1) in the reals and, for every actual bounded operator S on H, HasSum(k maps to Inner(u(k),S(u(k))),phi(S)) in the complexes. The family is chosen before S.")),
                Paragraph(Text("For a positive normalized functional f, the pre-GNS norm q(A) has q(1)=1, q(AB)<=||A||q(B), and |f(star(A)B)|<=q(A)q(B). Splitting S-PSP=(1-P)S+PS(1-P) gives |f(S)-f(PSP)|<=2||S||sqrt(Re(f(1-P))). This estimate controls arbitrary operators, including non-self-adjoint ones.")),
                Paragraph(Text("Write rankOne(x,y) for z maps to Inner(y,z)x. The continuous sesquilinear form phi(rankOne(u,v)) and Hilbert-space Riesz representation construct an actual positive bounded operator rho with Inner(y,rho(x))=phi(rankOne(x,y)). Its positive square root T satisfies T squared equals rho. Choose any Hilbert basis b, with no countability assumption, and put v(i)=T(b(i)). Finite orthonormal rank-one sums are star projections, and positivity of their complements gives sum over each finite set of ||v(i)||^2<=1.")),
                Paragraph(Text("The resulting mass m is at most one, and |Inner(v(i),S(v(i)))|<=||S||||v(i)||^2 makes every operator pairing summable. The vector-sum functional psi is positive. Parseval gives psi(rankOne(x,y))=Inner(T(y),T(x))=Inner(y,rho(x))=phi(rankOne(x,y)). Expanding the actual finite-dimensional range of any star projection P into an orthonormal basis gives psi(PSP)=phi(PSP), also when that range is zero.")),
                Paragraph(Text("Thus psi(E(j))=phi(E(j)) and Re(phi(E(j)))<=m. Tightness makes these values tend to one, so m=1 and psi(1)=1. Both normalized functionals have the same complement values at E(j); applying the compression estimate twice gives |phi(S)-psi(S)|<=4||S||sqrt(Re(phi(1-E(j)))). The right side tends to zero, proving agreement for every bounded S.")),
                Paragraph(Text("Summability of the squared norms makes the nonzero support of v countable. Inject that support into the natural numbers and extend its vectors by zero. The same reindexing preserves the real mass HasSum and each complex operator-pairing HasSum, producing the one family u required by the statement. Finite support and zero-rank compressions are included.")),
                Paragraph(Text("The GNS, Riesz, positive-square-root, Hilbert-basis, Parseval, finite-projection-expansion and countable-support results supply the individual steps. The argument combines them to construct a family from the given functional, obtain its mass from the given finite-rank tightness, and extend equality to all bounded operators. It requires no separability, normality, pre-existing vector ensemble, or spectral labeling.")),
                Paragraph(Text("This is a conditional finite-rank-tightness theorem. It does not derive tightness from position or momentum bounds, identify first operator domains, or establish covariance or a Gibbs representation."))),
            DescribeRole.Theorem))));
}
