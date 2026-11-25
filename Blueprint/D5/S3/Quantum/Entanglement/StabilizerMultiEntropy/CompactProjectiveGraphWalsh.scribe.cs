using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy;

internal sealed class CompactProjectiveGraphWalshDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/CompactProjectiveGraphWalsh.";
    private static readonly LibraryNoteRef Gce =
        LibraryNoteRef.Create("D5/L/QuantumStates/liu2025generalized");

    private static readonly LibraryNoteRef RankWidth =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/oum2005rankwidth");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual graph-state full Walsh coefficient is a binary projective characteristic product.",
        H("Characteristic cancellation for compact graph states"),
        Blocks(
            Describe.Lean(DescribeId.Create("compact-projective-walsh"),
                DeclarationHandle.Create(Owner + "compact_projective_walsh"),
                H("The full-system Walsh factor of the compact projective graph"),
                StatementSource.FromAuthor(CompactStatement()), AssessedProvenance.FromRepo(RankWidth, Gce),
                Blocks(
                    Paragraph(Text("For each n, use every nonzero vector over the binary field in dimension n + 1 and one parallel copy "
                        + "of a basis vector. The fundamental graph of the resulting systematic chart has exactly 2^(n + 1) sites, "
                        + "including the basis sites but no ancillary coordinate or zero-vector sites. The observable is the normalized reduced "
                        + "graph-state matrix's actual real power trace at each subsystem. W is its alternating full-system sum; its candidate "
                        + "probability mass is W divided by 2 to the number of sites.")),
                    Paragraph(Text("Oum's Proposition 3.1 expresses a cut rank as the sum of the two restriction ranks minus total rank "
                        + "in this normalization. On a cut with neither side spanning, the residual is an exact product of the two rank defects in the powers. One cut side spans here because two proper binary subspaces cannot cover all points. "
                        + "Under this condition the cut moment is the sum of the two restriction-rank powers minus the full-rank power. "
                        + "Complementing the mask aligns the even full-system signs and the constant cancels. Grouping the two parallel "
                        + "copies gives the three weights -1, -1, +1, so their total agrees with a single copy. The resulting signed sum "
                        + "is the binary projective characteristic product, namely twice the product of (1 − 2^j/q) over 0 ≤ j ≤ n.")),
                    Paragraph(Text("Let q be 2^(K-1). For the graph of dimension m + 2, only the last product factor is negative when "
                        + "2^m < q < 2^(m+1). The full-system Walsh numerator is strictly negative on "
                        + "this entire band. This does not claim that every graph fails at noninteger order, or that this size "
                        + "is optimal for every band."))),
                DescribeRole.Theorem))));

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula domain, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), domain, body);
    private static Formula All(string name, Formula domain, Formula body) =>
        Bind(FormulaQuantifier.ForAll, name, domain, body);
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));

    private static Formula CompactStatement()
    {
        var k = F.Id("K");
        var n = F.Id("n");
        var m = F.Id("m");
        var q = Call("q", k);
        var nat = Seq(Mathbb, Grp(F.Id("N")));
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var factor = All("n", nat, Equal(Call("W", k, n), Call("ProjectiveFactor", q, n)));
        var band = All("m", nat, Implies(Call("OpenDyadicBand", q, m),
            new Formula.Relation(Call("W", k, new Formula.Binary(m, FormulaBinaryOperator.Add, Num(1))),
                FormulaRelationOperator.LessThan, Num(0))));
        var consequence = new Formula.Logic(P(factor), FormulaLogicOperator.And, P(band));
        return Disp(All("K", real, Implies(
            new Formula.Relation(Num(1), FormulaRelationOperator.LessThan, k), consequence)));
    }

}
