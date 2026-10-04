using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class CompletedProductL2Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The completed complex Hilbert tensor of sigma-finite L2 spaces is the product L2 space by multiplication of AE representatives.",
        H("Completed Product L2 Unitary"),
        Blocks(Describe.Lean(
            DescribeId.Create("completed-product-l2-unitary"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/CompletedProductL2.exists_completed_product_unitary"),
            H("Actual function-product unitary"),
            StatementSource.FromAuthor(Disp(Seq(
                Forall, Sp, F.Id("X"), InMacro, Call("MeasurableSpaces"), Comma, Esc,
                Forall, Sp, F.Id("Y"), InMacro, Call("MeasurableSpaces"), Comma, Esc,
                Forall, Sp, Mu, InMacro, Call("SigmaFiniteMeasures", F.Id("X")), Comma, Esc,
                Forall, Sp, Nu, InMacro, Call("SigmaFiniteMeasures", F.Id("Y")), Comma, Esc,
                Exists, Sp, F.Id("U"), InMacro,
                Call("UnitaryC",
                    Call("Completion", Call("HilbertTensor",
                        Call("L2", F.Id("X"), Mu),
                        Call("L2", F.Id("Y"), Nu))),
                    Call("L2", Seq(F.Id("X"), Sp, Times, Sp, F.Id("Y")), Seq(Mu, Times, Nu))),
                Comma, Esc,
                Forall, Sp, F.Id("f"), InMacro, Call("L2", F.Id("X"), Mu), Comma, Esc,
                Forall, Sp, F.Id("g"), InMacro, Call("L2", F.Id("Y"), Nu), Comma, Esc,
                Call("aeEqual", Seq(Mu, Times, Nu),
                    Call("Representative", Call("U", Call("iota",
                        Call("tensor", F.Id("f"), F.Id("g"))))),
                    Seq(Open, F.Id("x"), Comma, F.Id("y"), Close, Mapsto,
                        Call("f", F.Id("x")), Call("g", F.Id("y"))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/mathlib2025hilberttensor")),
            Blocks(
                Paragraph(Text("MeasurableSpaces ranges over arbitrary types with measurable-space structures. SigmaFiniteMeasures(X) comprises all sigma-finite measures on X. L2(X,mu) means complex Lp at exponent 2. HilbertTensor is the algebraic complex tensor with its actual inner-product tensor norm, Completion is its metric completion, and iota is the canonical completion embedding. UnitaryC(A,B) denotes the complex linear isometric equivalences from A onto B. Representative chooses an AE representative, and aeEqual(eta,a,b) is equality eta-almost everywhere.")),
                Paragraph(Text("Both measures are arbitrary sigma-finite measures. The domain is the actual completion of the algebraic tensor with Mathlib's inner-product tensor norm. The target is complex L2 of the actual product measure. The naturality clause holds for every pair of factor L2 vectors and is an almost-everywhere representative equality.")),
                Paragraph(Text("Square integrability of the product and complex Fubini give an inner-preserving algebraic lift for all finite sums. The existing completion extension preserves its isometry. Finite measurable rectangle tests, localization to finite exhaustive rectangles, and pi-system induction show that its closed range has zero orthogonal complement; orthogonal projection gives surjectivity.")),
                Paragraph(Text("Finite Euclidean factors, including empty coordinate types, satisfy these hypotheses. Physical coordinate pullback and the mass-one scalar empty factor are applications of existing measure-preserving and constant-L2 APIs. No basis, density, desired unitary, finite total volume or finite Hilbert dimension is assumed.")),
                Paragraph(Text("This theorem supplies the completed function-space tensor bridge. Physical Hamiltonian domains, selfadjointness, metaplectic covariance, the same-H Gibbs trace and thermal operator factorization require additional results."))),
            DescribeRole.Theorem))));
}
