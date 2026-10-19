using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Convolution;

internal sealed class PerfectMatchingCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/Convolution/PerfectMatchingCount.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Count fixed-point-free involutions using the pinned Mathlib cycle-type formula.",
        H("Perfect Matching Count"),
        Blocks(
            Paragraph(Text(
                "The proof specializes Equiv.Perm.card_of_cycleType_mul_eq to h cycles "
                + "of length two. It supplies the cross-edge factor for the proposed "
                + "MatchingMonomialFiber equivalence.")),
            Describe.Lean(
                DescribeId.Create("involution-cycle-type"),
                DeclarationHandle.Create(Prefix + "involution_iff_cycleType"),
                H("Pairing involutions and their cycle type"),
                StatementSource.FromAuthor(InvolutionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite type of cardinality 2h, a permutation is an involution "
                    + "without fixed points exactly when its cycle type consists of h copies "
                    + "of two. The type and its decidable equality are arbitrary."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("involution-count-product"),
                DeclarationHandle.Create(Prefix + "card_fixedPointFreeInvolution_mul"),
                H("Exact Product Count"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite type of cardinality 2h, its number of fixed-point-free "
                    + "involutions times h! times 2^h equals (2h)!."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("involution-count-quotient"),
                DeclarationHandle.Create(Prefix + "card_fixedPointFreeInvolution"),
                H("Factorial Quotient Count"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Positivity of the denominator turns the product equality into the "
                    + "exact natural-number factorial quotient, including h = 0."))),
                DescribeRole.Theorem))));

    private static Formula InvolutionFormula()
    {
        Formula a = F.Id("A");
        Formula h = F.Id("h");
        Formula p = F.Id("p");
        Formula x = F.Id("x");
        Formula count = new Formula.Relation(At(Q("Fintype", "card"), a),
            FormulaRelationOperator.Equal, new Formula.Binary(D(2), FormulaBinaryOperator.Multiply, h));
        Formula noFixed = All("x", a,
            new Formula.Relation(At(p, x), FormulaRelationOperator.NotEqual, x));
        Formula involutive = new Formula.Logic(
            Parenthesized(At(Q("Function", "Involutive"), p)), FormulaLogicOperator.And,
            Parenthesized(noFixed));
        Formula cycleType = new Formula.Relation(At(Q("Equiv", "Perm", "cycleType"), p),
            FormulaRelationOperator.Equal, At(Q("Multiset", "replicate"), h, D(2)));
        Formula equivalence = new Formula.Logic(Parenthesized(involutive),
            FormulaLogicOperator.Iff, Parenthesized(cycleType));
        return Disp(Seq(Forall, Sp, Typed(a, Seq(Q("Type"), Star)), Sp,
            OpenBracket, At(Q("Fintype"), a), CloseBracket, Sp,
            OpenBracket, At(Q("DecidableEq"), a), CloseBracket, Comma, Sp,
            Parenthesized(All("h", Seq(Mathbb, Grp(F.Id("N"))),
                new Formula.Logic(Parenthesized(count), FormulaLogicOperator.Implies,
                    Parenthesized(All("p", At(Q("Equiv", "Perm"), a),
                        equivalence)))))));
    }

    private static Formula Q(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(F.Id(name), type), Comma, Sp, Parenthesized(body));
}
