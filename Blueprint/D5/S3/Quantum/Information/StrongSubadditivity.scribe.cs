using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class StrongSubadditivityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/StrongSubadditivity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strong subadditivity for actual finite density matrices, including singular states.",
        H("Actual Density Strong Subadditivity"),
        Blocks(
            Paragraph(Text("The supplier is Physlib at immutable revision "
                + "2725b6f621901d4cd330869e9b77105045c1582e. Its original Apache-2.0 "
                + "copyright notices and proof bodies are retained in the consumed D5 closure. "
                + "The receiving carrier is the project's PSD trace-one CStarMatrix. "
                + "toMState keeps exactly the same complex matrix. Both actual partial traces "
                + "agree entry by entry, including after the tensor associator. "
                + "This is an integration of an existing theorem, with no novelty claim. "
                + "Library/Divergence/meiburg2026ssa.md records all 32 consumed modules, "
                + "their immutable upstream source mapping and adaptations, the original "
                + "Meiburg/Lessa/Soldati attribution, and the full Apache-2.0 license "
                + "retained in the supplier ForMathlib/Misc.lean.")),
            Result("entropy-normalization", "entropy_toMState", "The entropy normalization agrees",
                "Continuous functional calculus transports through the CStarMatrix star algebra "
                    + "equivalence. Both entropies are the natural-logarithm trace of negative "
                    + "x log x. Zero eigenvalues contribute zero, so no positive-definite or "
                    + "support condition is added.",
                Disp(Seq(Call("Svn", Call("toMState", Rho)), Sp, Eq, Sp, Call("S", Rho)))),
            Result("ssa", "strong_subadditivity", "Strong subadditivity on actual marginals",
                "For arbitrary finite A, B, C and every DensityState on A tensor B tensor C, "
                    + "S(ABC)+S(B) is at most S(AB)+S(BC). marginalLeft traces the left factor; "
                    + "marginalRight traces the right factor. The AB state is the actual right "
                    + "partial trace after the associator, and B is the actual right trace of BC. "
                    + "No SSA, DPI, invertibility, or entropy-equality hypothesis is supplied.",
                Disp(Seq(Call("S", F.Id("ABC")), Sp, Plus, Sp, Call("S", F.Id("B")),
                    Sp, Le, Sp, Call("S", F.Id("AB")), Sp, Plus, Sp,
                    Call("S", F.Id("BC"))))))));

    private static DocumentBlock Result(string id, string declaration, string title,
        string text, Formula formula) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
