using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class SectorSchmidtEncodingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Entanglement/SectorSchmidtEncoding.";

    public DocumentDefinition Create()
    {
        Formula sector = F.Id("Sector"), coord = F.Id("Coord"), d = F.Id("d");
        Formula spectrum = F.Id("spectrum"), x = F.Id("x"), y = F.Id("y"), s = F.Id("s");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula Source(Formula body) => All(
            [Bound("Sector", F.Id("FiniteType")), Bound("Coord", F.Id("FiniteType")),
                Bound("d", Call("Function", sector, natural))], body);
        Formula Target(Formula body) => All(
            [Bound("Sector", F.Id("FiniteType")),
                Bound("d", Call("Function", sector, natural))], body);
        Formula Rank = Call("ofNat", Call("apply", d, Call("sector", x)));
        Formula Condition = And(Eqn(x, y), Eqn(Call("sector", x), s));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Dependent sector coordinates and the normalized source and flat target encoding matrices.",
            H("Sector Schmidt Encodings"),
            Blocks(
                Paragraph(Text(
                    "Sector and Coord are finite types with decidable equality. The natural number "
                    + "d(s) is the target rank of sector s. sourceFiber(d,Coord,s) is Fin(d(s)) "
                    + "times Coord, while targetFiber(d,s) is Fin(d(s)). Sigma forms the dependent "
                    + "sum over Sector. Each such coordinate x has sector(x); a source coordinate "
                    + "also has residual(x) in Coord. ofNat and ofReal denote the real and "
                    + "complex scalar embeddings.")),
                Item("SourceLocal", "Source coordinates", Source(Eqn(
                    Call("SourceLocal", d, coord),
                    Call("Sigma", sector, Call("sourceFiber", d, coord)))),
                    "A source coordinate contains its sector, one target coordinate, and one residual spectral coordinate."),
                Item("TargetLocal", "Target coordinates", Target(Eqn(
                    Call("TargetLocal", d), Call("Sigma", sector, Call("targetFiber", d)))),
                    "A target coordinate contains its sector and one coordinate within the sector rank."),
                Item("sourceEncoding", "Source encoding matrix", Source(All(
                    [Bound("spectrum", Call("Function", sector, Call("Function", coord, real))),
                        Bound("x", Call("SourceLocal", d, coord)),
                        Bound("y", Call("SourceLocal", d, coord)), Bound("s", sector)],
                    Eqn(Call("entry", Call("sourceEncoding", d, spectrum), Call("pair", x, y), s),
                        Call("ite", Condition, Call("ofReal", Call("sqrt",
                            Divide(Call("apply", spectrum, Call("sector", x), Call("residual", x)), Rank))),
                            Num(0))))),
                    "The source matrix is diagonal across the two physical sides. In sector s each residual value is repeated d(s) times, with amplitude sqrt(spectrum(s,j)/d(s)). Positive ranks and normalized nonnegative spectra make these columns unit vectors; distinct sector columns have disjoint support."),
                Item("targetEncoding", "Flat target encoding matrix", Target(All(
                    [Bound("x", Call("TargetLocal", d)), Bound("y", Call("TargetLocal", d)),
                        Bound("s", sector)],
                    Eqn(Call("entry", Call("targetEncoding", d), Call("pair", x, y), s),
                        Call("ite", Condition, Call("ofReal", Call("sqrt", Call("inv", Rank))), Num(0))))),
                    "The target matrix has equal amplitude sqrt(1/d(s)) on the diagonal coordinates of sector s. Positive sector ranks make its columns unit vectors with disjoint sector supports."))));
    }

    private static DocumentBlock Item(string name, string title, Formula formula, string explanation) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Owner + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] vars, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. vars], body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Divide(Formula left, Formula right) =>
        Seq(Frac, Grp(left), Grp(right));
}
