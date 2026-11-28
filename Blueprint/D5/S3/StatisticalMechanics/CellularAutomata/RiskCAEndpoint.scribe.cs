using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.CellularAutomata;

internal sealed class RiskCAEndpointDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/StatisticalMechanics/CellularAutomata/RiskCAEndpoint.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/ariasnoguerales2026riskca");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A collision in the deterministic RiskCA at the highest active threshold.",
        H("Noninjectivity on complete finite boards"),
        Blocks(Describe.Lean(
            DescribeId.Create("riskca-highest-active-threshold-noninjective"),
            DeclarationHandle.Create(Owner + "paper_noninjective"),
            H("The zero-growth step has a collision"),
            StatementSource.FromAuthor(Collision()), AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text("Let V be the vertex set of a finite complete simple graph with at least two vertices, let P ≥ 2 be the number of available owner labels, and let M ≥ 3 be the unit capacity. For every fixed priority permutation of V, either fortification setting, and every real 1 < ρ < 2, Φ denotes the deterministic local step of §3.2 and Appendix B Algorithm 1 with growth zero and threshold M − 1. Its carrier S is the full product of the owner and unit alphabets over V. Equality of configurations is pointwise.")),
                Paragraph(Text("Choose distinct vertices u and v. Put M units at u and one unit everywhere else. Assign one owner to v and a different owner everywhere else. The unique request is from u to v. Its pre-commit force is M − 1, its post-commit defence is one, and the strict win leaves M − 2 units at v. The output Y has one owner and one unit everywhere except at v. Its threats vanish and the zero-growth step fixes it. The inputs differ at u, giving Φ(X) = Y = Φ(Y)."))),
            DescribeRole.Theorem))));

    private static Formula Collision()
    {
        Formula x = F.Id("X"), y = F.Id("Y"), space = F.Id("S");
        Formula StepAt(Formula state) => Seq(F.Greek("Phi"), Open, state, Close);
        return Disp(Seq(Exists, Sp, x, Comma, y, Sp, InMacro, Sp, space, Comma, Sp,
            x, Sp, Neq, Sp, y, Sp, Land, Sp, StepAt(x), Sp, Eq, Sp, StepAt(y)));
    }
}
