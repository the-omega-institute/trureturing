using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CircularWords;

internal sealed class PairedDeletionSharpnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CircularWords/PairedDeletionSharpness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every finite support with at least four labels and every three distinct supported labels, native real probability laws on actual cycles attain source total variation one and paired-deletion readout total variations one third on each of two overlapping channels.",
        H("Sharpness of Overlapping Paired-Deletion Stability"), Blocks(
            Paragraph(Text("For every finite support with at least four labels and every three distinct supported labels a, b, c, there are two genuine probability measures on legal oriented cycles whose source total variation is one while the two overlapping paired-deletion readouts (D_a,D_b) and (D_b,D_c) each retain total variation exactly one third. The construction is carried by six actual rotation classes.")),
            Describe.Lean(DescribeId.Create("real-paired-deletion-sharpness"),
                DeclarationHandle.Create(Prefix + "real_probability_paired_deletion_sharpness"),
                H("Native real-law sharpness and coefficient obstructions"),
                StatementSource.FromAuthor(SharpnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Choose the six actual cycles C=[a,b,c,L], CF=[b,a,c,L], CG=[a,c,b,L], E=[c,b,a,L], EF=[c,a,b,L], and EG=[b,c,a,L]. The first law puts mass one third on CF, CG, and E; the second puts mass one third on C, EF, and EG. A rooted insertion argument proves that these are six distinct rotation classes and that every class has support exactly A.")),
                    Paragraph(Text("For F=(D_a,D_b), the pairs from CF and C coincide, as do the pairs from E and EF; after cancellation the signed difference is a dipole of two distinct output atoms with weights plus or minus one third. The same calculation for G=(D_b,D_c) cancels CG with C and E with EG. Substitution into a universal sum or maximum inverse inequality gives K at least 3/2 or 3.")),
                    Paragraph(Text("The theorem uses native ProbabilityMeasure values and the repository's real finite half-l1 total variation. It is a lower-bound sharpness result; a matching general upper bound is a separate question.")))),
            Paragraph(Text("The proof has standard kernel axiom closure only: propext, Classical.choice, and Quot.sound.")))));

    private static Formula SharpnessFormula()
    {
        Formula rho = F.Id("rho"), sigma = F.Id("sigma");
        Formula source = Eq(Call("TV", rho, sigma), D(1));
        Formula first = Eq(Call("TV", Call("Fstar", rho), Call("Fstar", sigma)), Fraction(D(1), D(3)));
        Formula second = Eq(Call("TV", Call("Gstar", rho), Call("Gstar", sigma)), Fraction(D(1), D(3)));
        return Disp(And(source, And(first, second)));
    }

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Seq(Open, x, Close), FormulaLogicOperator.And, Seq(Open, y, Close));
    private static Formula Fraction(Formula x, Formula y) => new Formula.Fraction(x, y);
}
