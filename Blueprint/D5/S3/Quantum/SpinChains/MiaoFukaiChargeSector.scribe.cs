using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class MiaoFukaiChargeSectorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/MiaoFukaiChargeSector.";
    private static readonly Formula L = F.Id("L");
    private static readonly Formula HMin = F.Id("h");
    private static readonly Formula B = F.Id("b");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A recoverable binary tile code gives a jammed family at a common charge.",
        H("An odd-deficit sector of the periodic ladder"),
        Blocks(
            Paragraph(Text("Let m be the floor of (L−8)/5. The tiles A and B comprise a minus rung followed by one and two empty rungs, respectively. Each of the m five-rung blocks independently reads AB or BA. At zero-based site 5i+2, those two choices read minus and empty, respectively. Reading that coordinate recovers the bit in each block, so the construction is injective on labelled words.")),
            Paragraph(Text("The residual length r=L−5m−6 lies between two and six. Its tail, in increasing order of r, is A, B, AA, AB, or BB. The respective numbers of one-empty gaps are 1, 0, 2, 1, and 0. If m plus that tail count is even, the six-rung pad is AAA, which adds three one-empty gaps. Otherwise the pad is BB, which adds none.")),
            Paragraph(Text("Every tile starts occupied and ends empty, so blockade holds at the periodic seam and each join. The only zero projector values occur at the one-empty gaps. Their neighbours have projector value one. Thus the sum of projector values is the length minus the number of one-empty gaps and every word is jammed.")),
            Theorem("tile-word", "The sector embedding recovers the tile word", "jamEmbedding_val",
                Lengths(All(B, Seq(Call("Fin", Call("blocks", L)), To, Call("Bool")),
                    new Formula.Relation(Call("val", Call("jamEmbedding", HMin, B)),
                        FormulaRelationOperator.Equal, Call("tiledConfig", HMin, B)))),
                "The two maps use the same labelled configurations, including across the seam."),
            Theorem("odd-deficit", "Parity of the common charge deficit", "target_deficit_odd",
                LengthHypothesis(Call("Odd", Seq(L, Minus, Call("targetCharge", L)))),
                "The parity-dependent pad makes the deficit odd for every length at least twelve."))));

    private static DocumentBlock Theorem(string id, string title, string name, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("miao-fukai-" + id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var symbol = Seq(Operatorname, Grp(F.Id(name)));
        return arguments.Length == 0 ? symbol : new Formula.Apply(symbol, [.. arguments]);
    }

    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, variable, Colon, Sp, type, Close, Comma, Sp, body);
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula LowerBound => new Formula.Relation(D(1, 2), FormulaRelationOperator.LessThanOrEqual, L);
    private static Formula Lengths(Formula body) => All(L, Nat, All(HMin, LowerBound, body));
    private static Formula LengthHypothesis(Formula body) =>
        All(L, Nat, new Formula.Logic(LowerBound, FormulaLogicOperator.Implies, body));
}
