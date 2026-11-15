using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.PermutationCriteria;

internal sealed class LabelRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/PermutationCriteria/LabelRecovery.";

    public DocumentDefinition Create()
    {
        Formula i = F.Id("i"), j = F.Id("j"), f = F.Id("f"), g = F.Id("g");
        Formula sites = F.Id("I"), bits = Call("Bool"), pair = Call("prod", bits, bits);
        Formula labels = Seq(sites, To, pair);
        Formula fi = At(f, i), fj = At(f, j), gi = At(g, i), gj = At(g, j);
        Formula s = F.Id("s"), c = F.Id("c");
        Formula side = All(i, sites,
            new Formula.Logic(Call("sameSide", fi), FormulaLogicOperator.Iff, Call("sameSide", gi)));
        Formula distances = All(i, sites, All(j, sites,
            Equal(Call("pairDistance", fi, fj), Call("pairDistance", gi, gj))));
        Formula conclusion = Ex(s, bits, Ex(c, bits, All(i, sites,
            Equal(gi, Call("transform", s, c, fi)))));
        Formula statement = All(sites, Call("Type"), All(f, labels, All(g, labels,
            new Formula.Logic(Par(side), FormulaLogicOperator.Implies,
                new Formula.Logic(Par(distances), FormulaLogicOperator.Implies, conclusion)))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Paired Boolean labels are determined by same-side membership and all pair distances, up to four global symmetries.",
            H("Recovering paired Boolean labels"),
            Blocks(Describe.Lean(
                DescribeId.Create("paired-boolean-label-recovery"),
                DeclarationHandle.Create(Prefix + "recover_labels"),
                H("Pair distances recover the four symmetry classes"),
                StatementSource.FromAuthor(Disp(statement)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The carrier I is an arbitrary type, including the empty type. A label is an ordered pair of Boolean values. "
                    + "sameSide(x) means that the two coordinates of x agree; pairDistance counts coordinate disagreements. "
                    + "The hypotheses preserve sameSide at every site and pairDistance for every ordered pair of sites. "
                    + "Within either sameSide sector, distance zero distinguishes equal first coordinates from unequal ones. "
                    + "The first coordinates therefore change by one constant Boolean XOR in each sector. "
                    + "The two sector constants combine into a global exchange of coordinates and a global simultaneous complement. "
                    + "transform(s,c,x) first exchanges coordinates when s is true, then applies XOR with c to both coordinates. "
                    + "Its four choices are the identity, simultaneous complement, coordinate exchange, and their composite."))),
                DescribeRole.Theorem)),
            []));
    }

    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula At(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula All(Formula x, Formula domain, Formula body) =>
        Seq(Forall, Sp, x, Colon, domain, Comma, Sp, Par(body));
    private static Formula Ex(Formula x, Formula domain, Formula body) =>
        Seq(Exists, Sp, x, Colon, domain, Comma, Sp, Par(body));
}
