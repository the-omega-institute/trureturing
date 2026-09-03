using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ReflectedSpectrum;

internal sealed class ConfluentNegativeJetBlockDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/ReflectedSpectrum/ConfluentNegativeJetBlock.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An invertible jet multiplier transports Hardy positivity to strict negativity "
            + "and exact finite negative inertia.",
        H("Confluent Negative Jet Block"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("confluent-negative-jet-block"),
                DeclarationHandle.Create(Prefix + "confluent_negative_jet_block"),
                H("The confluent jet block is strictly negative"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source's analytic zero cancellation and multiplication Leibniz "
                            + "rule are recorded as the factorization G equals minus L star H L. "
                            + "The Hardy derivative-evaluation Gram matrix H is positive "
                            + "definite, and the lower-triangular jet multiplier L is invertible.")),
                    Paragraph(Text(
                        "Positive definiteness is preserved by invertible congruence. Hence "
                            + "minus G is positive definite, so G is strictly negative definite. "
                            + "All m eigenvalues are negative, giving exact negative index m and "
                            + "therefore the stated lower bound with equality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("confluent-negative-jet-block-index-lower-bound"),
                DeclarationHandle.Create(
                    Prefix + "confluent_negative_jet_block_index_lower_bound"),
                H("Exact inertia implies the source lower bound"),
                StatementSource.FromAuthor(LowerBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is the inequality-facing projection of the exact finite inertia "
                        + "theorem: the negative index is at least the jet order m."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula MatrixProduct(Formula left, Formula middle, Formula right) =>
        Seq(left, Sp, Times, Sp, middle, Sp, Times, Sp, right);

    private static Formula Factorization(
        Formula gram, Formula hardy, Formula multiplier) =>
        EqualTo(
            gram,
            Seq(
                Minus,
                Grp(MatrixProduct(
                    Call("conjTranspose", multiplier), hardy, multiplier))));

    private static Formula Premises(
        Formula gram, Formula hardy, Formula multiplier) =>
        And(
            Call("PosDef", hardy),
            And(
                Call("IsUnit", multiplier),
                And(Call("IsHermitian", gram), Factorization(gram, hardy, multiplier))));

    private static Formula TheoremFormula()
    {
        Formula natural = Call("Nat");
        Formula complex = Call("Complex");
        Formula m = F.Id("m");
        Formula hardy = F.Id("H");
        Formula multiplier = F.Id("L");
        Formula gram = F.Id("G");
        Formula finiteIndex = Call("Fin", m);
        Formula matrix = Call("Matrix", finiteIndex, finiteIndex, complex);
        Formula conclusion = And(
            Call("PosDef", Seq(Minus, gram)),
            EqualTo(Call("negIndex", gram), m));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("m", natural),
                Bound("H", matrix),
                Bound("L", matrix),
                Bound("G", matrix),
            ],
            Implies(Premises(gram, hardy, multiplier), conclusion)));
    }

    private static Formula LowerBoundFormula()
    {
        Formula natural = Call("Nat");
        Formula complex = Call("Complex");
        Formula m = F.Id("m");
        Formula hardy = F.Id("H");
        Formula multiplier = F.Id("L");
        Formula gram = F.Id("G");
        Formula finiteIndex = Call("Fin", m);
        Formula matrix = Call("Matrix", finiteIndex, finiteIndex, complex);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("m", natural),
                Bound("H", matrix),
                Bound("L", matrix),
                Bound("G", matrix),
            ],
            Implies(
                Premises(gram, hardy, multiplier),
                LessOrEqual(m, Call("negIndex", gram)))));
    }
}
