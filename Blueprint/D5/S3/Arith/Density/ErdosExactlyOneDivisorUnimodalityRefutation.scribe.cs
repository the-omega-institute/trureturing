using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Density;

internal sealed class ErdosExactlyOneDivisorUnimodalityRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Density/tenenbaum2013unconventional");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact periodic densities refute unimodality of the one-divisor interval density.",
        H("A Counterexample to One-Divisor Interval-Density Unimodality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("erdos-one-divisor-has-density"),
                DeclarationHandle.Create(Prefix + "hasDensity"),
                H("Natural density"),
                StatementSource.FromAuthor(HasDensityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A set has density delta when the proportion of its members in the "
                        + "first N natural numbers tends to delta as N tends to infinity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos-one-divisor-periodic-density"),
                DeclarationHandle.Create(Prefix + "hasDensity_of_periodic"),
                H("Density of a periodic set"),
                StatementSource.FromAuthor(PeriodicDensityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a positive period P, split N into complete periods and a remainder. "
                        + "The complete periods contribute the same count, while the remainder "
                        + "is bounded by P and vanishes after division by N."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("erdos-one-divisor-interval-predicate"),
                DeclarationHandle.Create(Prefix + "exactlyOneDivisorIn"),
                H("Exactly one divisor in an interval"),
                StatementSource.FromAuthor(ExactlyOneDivisorFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "An integer N satisfies the interval predicate when there is a unique "
                        + "divisor d strictly between n and m."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos-one-divisor-density-function"),
                DeclarationHandle.Create(Prefix + "epsOne"),
                H("The one-divisor interval density"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The value epsOne(n,m) is the natural density of integers having exactly "
                        + "one divisor in the open interval from n to m. It is set to zero if "
                        + "no such density exists; the periodic-density theorem proves existence."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos-one-divisor-unimodal"),
                DeclarationHandle.Create(Prefix + "Unimodal"),
                H("Weak unimodality on a tail"),
                StatementSource.FromAuthor(UnimodalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A function is weakly unimodal from lo when some mode m0 lies at or after "
                        + "lo, the function is nondecreasing from lo through m0, and it is "
                        + "nonincreasing from m0 onward."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos-one-divisor-printed-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The printed unimodality suggestion"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Erdős writes: Perhaps ε₁(n,m) is unimodular for m greater than "
                        + "n+1, but I know nothing about this. The tail begins at n+2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos-one-divisor-claim-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A strict valley refutes unimodality"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For n=2 the exact values at m=6, 7, and 8 are 13/30, 11/30, and "
                        + "13/35. The decrease followed by an increase contradicts either "
                        + "possible side of every proposed mode, so the printed assertion is false."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("erdos-1979-exactly-one-divisor-unimodality"),
                    ResolutionKind.Refuted)))));

    private static Formula HasDensityFormula()
    {
        var set = F.Id("A");
        var delta = DeltaLower;
        var index = F.Id("N");
        var count = Call("card", Call("filter", Call("range", index),
            LambdaTerm("k", Member(F.Id("k"), set))));
        var ratio = Divide(count, index);
        var limit = Call("Tendsto", LambdaTerm("N", ratio), F.Id("atTop"),
            Call("nhds", delta));
        return Disp(ForAll("A", SetsOfNaturals(),
            ForAll("delta", Reals(), Iff(Call("hasDensity", set, delta), limit))));
    }

    private static Formula PeriodicDensityFormula()
    {
        var set = F.Id("A");
        var period = F.Id("P");
        var membership = LambdaTerm("k", Member(F.Id("k"), set));
        var count = Call("card", Call("filter", Call("range", period), membership));
        return Disp(ForAll("A", SetsOfNaturals(), ForAll("P", Naturals(),
            Implies(Less(D(0), period),
                Implies(Call("Periodic", membership, period),
                    Call("hasDensity", set, Divide(count, period)))))));
    }

    private static Formula ExactlyOneDivisorFormula()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var number = F.Id("N");
        var divisor = F.Id("d");
        var unique = Seq(Exists, Bang, Sp, divisor, Colon, Sp, Naturals(), Comma, Sp,
            Parenthesized(And(Less(n, divisor), Less(divisor, m), Divides(divisor, number))));
        return Disp(ForAllMany([Bound("n", Naturals()), Bound("m", Naturals()),
            Bound("N", Naturals())],
            Iff(Call("exactlyOneDivisorIn", n, m, number), unique)));
    }

    private static Formula UnimodalFormula()
    {
        var function = F.Id("f");
        var lower = F.Id("lo");
        var mode = F.Id("m0");
        var a = F.Id("a");
        var b = F.Id("b");
        var increasing = ForAllMany([Bound("a", Naturals()), Bound("b", Naturals())],
            Implies(AtMost(lower, a), Implies(AtMost(a, b),
                Implies(AtMost(b, mode), AtMost(Apply(function, a), Apply(function, b))))));
        var decreasing = ForAllMany([Bound("a", Naturals()), Bound("b", Naturals())],
            Implies(AtMost(mode, a), Implies(AtMost(a, b),
                AtMost(Apply(function, b), Apply(function, a)))));
        var body = ExistsOneMode(mode, And(AtMost(lower, mode), increasing, decreasing));
        return Disp(ForAll("f", FunctionsNaturalsToReals(),
            ForAll("lo", Naturals(), Iff(Call("Unimodal", function, lower), body))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var function = LambdaTerm("m", Call("epsOne", n, m));
        return Disp(Iff(F.Id("claim"), ForAll("n", Naturals(),
            Call("Unimodal", function, Add(n, D(2))))));
    }

    private static Formula ResultFormula() => Disp(new Formula.Not(F.Id("claim")));

    private static Formula SetsOfNaturals() => Call("Set", Naturals());
    private static Formula FunctionsNaturalsToReals() =>
        Seq(Naturals(), Sp, To, Sp, Reals());
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula LambdaTerm(string name, Formula body) =>
        Seq(Lambda, Sp, F.Id(name), Comma, Sp, Parenthesized(body));
    private static Formula Divide(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Slash, Sp, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(F.Id(name), arguments);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies,
            Parenthesized(right));
    private static Formula And(params Formula[] values)
    {
        var result = Parenthesized(values[^1]);
        for (var index = values.Length - 2; index >= 0; index--)
            result = new Formula.Logic(Parenthesized(values[index]),
                FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula ForAllMany(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula ExistsOneMode(Formula mode, Formula body) =>
        Seq(Exists, Sp, mode, Colon, Sp, Naturals(), Comma, Sp, Parenthesized(body));
}
