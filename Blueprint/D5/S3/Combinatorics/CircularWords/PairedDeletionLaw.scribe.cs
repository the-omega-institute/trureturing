using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CircularWords;

internal sealed class PairedDeletionLawDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CircularWords/PairedDeletionLaw.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two overlapping paired deletion channels from the same original cycle determine every finite signed law, and therefore every probability law, on the complete fixed-support carrier.",
        H("Law Identification from Two Overlapping Paired Deletions"), Blocks(
            Paragraph(Text("Fix a finite support A with at least four labels and distinct supported labels a, b, c. "
                + "The two channels are F(C)=(D_a(C),D_b(C)) and G(C)=(D_b(C),D_c(C)); each pair is produced by the same source cycle. "
                + "Rotations are identified and reversal remains distinct.")),
            Describe.Lean(DescribeId.Create("signed-law-identification"),
                DeclarationHandle.Create(Prefix + "signed_injective"),
                H("Signed law identification on every finite legal realization"),
                StatementSource.FromAuthor(SignedFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any finite injective legal realization of the fixed-support cycles, equality of the two F pushforwards and equality of the two G pushforwards imply equality of the real signed weights. The proof uses the exact two-element R1 fibre classification: a non-singleton F fibre has a G-leaf, and the analogous statement holds with F and G exchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("full-signed-law-identification"),
                DeclarationHandle.Create(Prefix + "full_signed_injective"),
                H("Full fixed-support signed law identification"),
                StatementSource.FromAuthor(FullSignedFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The complete subtype of nodup oriented cycles with support exactly A is finite and nonempty. Applying the finite-realization theorem to its subtype value map gives injectivity for all real signed laws on the full legal carrier."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("full-probability-law-identification"),
                DeclarationHandle.Create(Prefix + "full_probability_injective"),
                H("Probability-law specialization"),
                StatementSource.FromAuthor(ProbabilityFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The probability statement records nonnegativity and unit total mass and then invokes the signed result. The construction is for the actual circular deletion maps and includes the cyclic cut and the card-four case."))),
                DescribeRole.Theorem),
            Paragraph(Text("A single paired channel can retain the adjacent-swap ambiguity classified in PairedDeletionFiber. The overlap through b supplies the singleton leaf that removes that ambiguity. No reversal quotient, abstract forest hypothesis, or three independent marginal law assumption is used.")))));

    private static Formula SignedFormula()
    {
        Formula i = F.Id("i"), mu = F.Id("mu"), nu = F.Id("nu"), f = F.Id("F"), g = F.Id("G");
        Formula premise = And(Eq(Call("pushforward", f, mu), Call("pushforward", f, nu)),
            Eq(Call("pushforward", g, mu), Call("pushforward", g, nu)));
        return Disp(All("ι", Call("Type"), Imp(premise, Eq(mu, nu))));
    }

    private static Formula FullSignedFormula()
    {
        Formula mu = F.Id("mu"), nu = F.Id("nu");
        Formula carrier = Call("FixedCycles", F.Id("A"));
        Formula premise = And(Eq(Call("pushforward", F.Id("F"), mu), Call("pushforward", F.Id("F"), nu)),
            Eq(Call("pushforward", F.Id("G"), mu), Call("pushforward", F.Id("G"), nu)));
        return Disp(All("A", Call("Finset", F.Id("α")), Imp(premise, Eq(mu, nu))));
    }

    private static Formula ProbabilityFormula()
    {
        Formula mu = F.Id("mu"), nu = F.Id("nu");
        Formula nonnegative = And(Call("Nonnegative", mu), Call("Nonnegative", nu));
        Formula unit = And(Eq(Call("mass", mu), D(1)), Eq(Call("mass", nu), D(1)));
        Formula channels = And(Eq(Call("Fstar", mu), Call("Fstar", nu)),
            Eq(Call("Gstar", mu), Call("Gstar", nu)));
        return Disp(Imp(And(nonnegative, And(unit, channels)), Eq(mu, nu)));
    }

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.And, Seq(Open, right, Close));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Implies, Seq(Open, right, Close));
}
