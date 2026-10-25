using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class EntanglementDepthGeneratorInjectivityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Partitions/EntanglementDepthGeneratorInjectivityRefutation.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Entropy/szalaytoth2025entanglementdepth");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct partitions have equal power sums at exponent one half and equal entanglement dimensions at base five halves.",
        H("Noninteger parameters do not ensure injectivity on integer partitions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("power-sum"),
                DeclarationHandle.Create(Prefix + "powerSum"),
                H("The real power sum"),
                StatementSource.FromAuthor(Disp(PowerSumFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a partition ξ of the natural number n and a real exponent q, powerSum sums "
                        + "the qth powers of the parts, including every repeated part with its multiplicity. "
                        + "Each natural part is cast to a real number before taking the real power. "
                        + "This is the power sum s_q of equation (sq), depths.tex lines 1903–1907. "
                        + "The source describes integer partitions as multisets of positive parts summing to n "
                        + "at lines 464–466; Nat.Partition n supplies this domain, including the empty partition at n = 0."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("entanglement-dimension"),
                DeclarationHandle.Create(Prefix + "entanglementDimension"),
                H("The entanglement dimension"),
                StatementSource.FromAuthor(Disp(EntanglementDimensionFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a real base d and a partition ξ of n, entanglementDimension sums d raised "
                        + "to each natural part, with multiplicity. The exponent remains a natural number. "
                        + "This is the function Dim_d of equation (Dimd), depths.tex lines 2306–2312. "
                        + "The definition permits every real d. The source's physical dimension satisfies d ≥ 2; "
                        + "for noninteger d the source treats d as a mathematical parameter at lines 2445–2447."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The disjunction of the two injectivity expectations"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The claim is the disjunction of two universal assertions suggested by Section 4.7, "
                        + "depths.tex lines 2437 and 2445–2447. The first asserts injectivity of powerSum "
                        + "on every Nat.Partition n for every real q unequal to the real cast of every natural k. "
                        + "The second asserts injectivity of entanglementDimension on every Nat.Partition n "
                        + "for every real d at least the real cast of the natural number two and unequal "
                        + "to the real cast of every natural k. Injectivity means that equality of values "
                        + "forces equality of the two partitions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Both universal injectivity assertions fail"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take the partitions {9, 1, 1, 1} and {4, 4, 4} of 12. "
                            + "Also take the partition of 26 with two parts equal to 3 and twenty parts equal to 1, "
                            + "and the partition of 26 with thirteen parts equal to 2. "
                            + "All parts are positive, and their sums are respectively 9 + 1 + 1 + 1 = 12, "
                            + "4 + 4 + 4 = 12, 3 + 3 + 20 = 26 and 13 · 2 = 26. "
                            + "The last partition is the specialization n = 26, y = 13, z = 0 of partition126, "
                            + "whose parts are n − 2y − 6z copies of 1, y copies of 2 and z copies of 6.")),
                    Paragraph(Text(
                        "The inequality half_noninteger says that an integer cast to the reals plus one half "
                            + "cannot equal the real cast of an integer. Apply it at integer shifts 0 and 2 "
                            + "and include each natural number into the integers. Reversing the inequalities "
                            + "shows that every natural cast differs from 1/2 and from 5/2.")),
                    Paragraph(Text(
                        "The first pair of partitions is distinct because 9 belongs to the first multiset "
                            + "and not to the second. The second pair is distinct because 3 belongs to the "
                            + "partition with two threes and not to the partition with thirteen twos.")),
                    Paragraph(Text(
                        "For real a and p, rpow_square_half gives (a²)^(p/2) = |a|^p. "
                            + "Use a = 3, p = 1 and then a = 2, p = 1. Positivity of 3 and 2 yields "
                            + "9^(1/2) = 3 and 4^(1/2) = 2. Since 1^(1/2) = 1, "
                            + "the first pair has powerSum values 3 + 1 + 1 + 1 = 6 and 2 + 2 + 2 = 6.")),
                    Paragraph(Text(
                        "At base 5/2, the second pair has entanglementDimension values "
                            + "2 · (5/2)³ + 20 · (5/2) = 325/4 and 13 · (5/2)² = 325/4. "
                            + "These are equal by rational arithmetic.")),
                    Paragraph(Text(
                        "Assume the disjunction claim and consider its two alternatives. "
                            + "The first alternative, at n = 12 and q = 1/2, would make the equal powerSum "
                            + "values force equality of the first pair, contradicting their distinctness. "
                            + "For the second alternative use n = 26 and d = 5/2. "
                            + "The base satisfies 2 ≤ 5/2 and is unequal to every natural cast. "
                            + "Injectivity would make the equal entanglementDimension values force equality "
                            + "of the second pair, again contradicting distinctness. Thus neither alternative holds."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("szalay-toth-2025-entanglement-depth-generator-injectivity"),
                    ResolutionKind.Refuted)))));

    private static Formula PowerSumFormula() =>
        All("n", Naturals(), All("q", Reals(), All("ξ", PartitionOf(X("n")),
            Equal(Typed(At(Local("powerSum"), NamedArg("n", X("n")), X("q"), X("ξ")), Reals()),
                At(Qualified("Multiset", "sum"),
                    At(Qualified("Multiset", "map"),
                        LambdaOf("x", Naturals(),
                            new Formula.Power(CastReal(X("x")), X("q"))),
                        At(Qualified("Nat", "Partition", "parts"), X("ξ"))))))));

    private static Formula EntanglementDimensionFormula() =>
        All("n", Naturals(), All("d", Reals(), All("ξ", PartitionOf(X("n")),
            Equal(Typed(At(Local("entanglementDimension"), NamedArg("n", X("n")), X("d"), X("ξ")), Reals()),
                At(Qualified("Multiset", "sum"),
                    At(Qualified("Multiset", "map"),
                        LambdaOf("x", Naturals(), new Formula.Power(X("d"), X("x"))),
                        At(Qualified("Nat", "Partition", "parts"), X("ξ"))))))));

    private static Formula ClaimFormula() =>
        Equal(Typed(Local("claim"), Qualified("Prop")), Parenthesized(Disjunction(
            All("n", Naturals(), All("q", Reals(),
                Arrow(All("k", Naturals(), NotEqual(CastReal(X("k")), X("q"))),
                    At(Qualified("Function", "Injective"),
                        At(Local("powerSum"), NamedArg("n", X("n")), X("q")))))),
            All("n", Naturals(), All("d", Reals(),
                Arrow(LE(CastReal(Typed(D(2), Naturals())), X("d")),
                    Arrow(All("k", Naturals(), NotEqual(CastReal(X("k")), X("d"))),
                        At(Qualified("Function", "Injective"),
                            At(Local("entanglementDimension"), NamedArg("n", X("n")), X("d"))))))))));

    private static Formula X(string name) => name == "ξ" ? Xi : F.Id(name);
    private static Formula Local(string name) => Qualified("D5", "S3", "Combinatorics", "Partitions",
        "EntanglementDepthGeneratorInjectivityRefutation", name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula NamedArg(string name, Formula value) => Parenthesized(Seq(X(name), Sp, Colon, Eq, Sp, value));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula PartitionOf(Formula n) => At(Qualified("Nat", "Partition"), n);
    private static Formula CastReal(Formula value) => Typed(At(Qualified("Nat", "cast"), value), Reals());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Disjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
}
