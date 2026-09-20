using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class FlorezCubicLatticePlanePathCountRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/florez2018cubiclattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both printed plane-count conjectures fail at path length three.",
        H("Flórez--Junes--Ramírez Cubic-Lattice Plane-Path Counts"),
        Blocks(
            Node("florez-signed-step", "Signed coordinate steps", "Step", StepFormula(),
                "A step chooses one of the three coordinate axes and one of two signs. "
                    + "The Fin(3) values 0, 1, and 2 represent the printed axes 1, 2, and 3; "
                    + "the Boolean component represents the sign.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("florez-path", "Paths from the origin", "Path", PathFormula(),
                "A path of length k is a sequence of k signed coordinate steps. Its initial "
                    + "vertex is the origin, as in the source definition.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("florez-partial-sum", "Initial-subpath coordinate vector", "partialSum",
                PartialSumFormula(),
                "For an axis c, partialSum(P,r)(c) sums the signed contributions on c from "
                    + "exactly those step indices i with i < r. This is the source vector V_r.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("florez-c-three-plus", "The printed C-three-plus predicate", "InCThreePlus",
                InCThreePlusFormula(),
                "The third coordinate is nonnegative after every nonempty prefix and is zero "
                    + "after the complete path. A binder r : Fin(k+1), together with 0 < val(r), "
                    + "ranges over exactly the printed indices 0 < r <= k.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("florez-xz-plane", "Complete containment in the xz-plane", "InXzPlane",
                PlaneFormula("InXzPlane", 1),
                "Every noninitial vertex has second coordinate zero. The omitted initial vertex "
                    + "is the origin and therefore already lies in the xz-plane.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("florez-yz-plane", "Complete containment in the yz-plane", "InYzPlane",
                PlaneFormula("InYzPlane", 0),
                "Every noninitial vertex has first coordinate zero. The omitted initial vertex "
                    + "is the origin and therefore already lies in the yz-plane.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("florez-c-three-plus-decidable", "Decidability of C-three-plus membership",
                "instDecidablePredInCThreePlus", DecidablePredicateFormula("InCThreePlus"),
                "This instance unfolds InCThreePlus once so finite universal quantification can "
                    + "be decided. It changes no truth value.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("florez-xz-plane-decidable", "Decidability of xz-plane containment",
                "instDecidablePredInXzPlane", DecidablePredicateFormula("InXzPlane"),
                "This instance unfolds InXzPlane once so finite universal quantification can be "
                    + "decided. It changes no truth value.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("florez-yz-plane-decidable", "Decidability of yz-plane containment",
                "instDecidablePredInYzPlane", DecidablePredicateFormula("InYzPlane"),
                "This instance unfolds InYzPlane once so finite universal quantification can be "
                    + "decided. It changes no truth value.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("florez-xz-count", "The printed-reading xz-plane count", "xzCount",
                CountFormula("xzCount", "InXzPlane"),
                "The count is the cardinality of the full finite path space filtered by both "
                    + "InCThreePlus and InXzPlane.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("florez-yz-count", "The printed-reading yz-plane count", "yzCount",
                CountFormula("yzCount", "InYzPlane"),
                "The count is the cardinality of the full finite path space filtered by both "
                    + "InCThreePlus and InYzPlane.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("florez-printed-formula", "The printed binomial sum", "formula",
                FormulaDefinition(),
                "The index set is the inclusive interval from 1 through k+1. The function "
                    + "binom(n,j) denotes Nat.choose(n,j), and NatDiv denotes natural-number "
                    + "integer division. Each displayed division is exact by the central-binomial "
                    + "divisibility identity.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("florez-conjecture-one", "Conjecture 1 as printed", "claim1",
                ClaimFormula("claim1", "xzCount"),
                "The paper states: \"Conjecture 1: For k ≥ 1, the number of paths in "
                    + "C_3^+(k) that are completely contained in the xz-plane is (see Table 4 "
                    + "first line) Σ_{i=1}^{k+1} \\binom{2i}{i}\\binom{k}{i−1}/(i+1).\"",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("florez-conjecture-two", "Conjecture 2 as printed", "claim2",
                ClaimFormula("claim2", "yzCount"),
                "The paper states: \"Conjecture 2: For k ≥ 1, the number of paths in "
                    + "C_3^+(k) that are completely contained in the yz-plane is "
                    + "Σ_{i=1}^{k+1} \\binom{2i}{i}\\binom{k}{i−1}/(i+1).\"",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("florez-conjecture-one-refuted", "Conjecture 1 is false", "result1",
                ResultFormula("claim1"),
                "At k = 3, the printed xz-plane predicate selects 14 of the 216 signed "
                    + "three-step paths, while the printed formula equals 36. Hence the universal "
                    + "claim is false.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "florez-junes-ramirez-cubic-lattice-xz-plane-path-count-refutation"),
                    ResolutionKind.Refuted)),
            Node("florez-conjecture-two-refuted", "Conjecture 2 is false", "result2",
                ResultFormula("claim2"),
                "At k = 3, the printed yz-plane predicate selects 14 of the 216 signed "
                    + "three-step paths, while the printed formula equals 36. Hence the universal "
                    + "claim is false.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "florez-junes-ramirez-cubic-lattice-yz-plane-path-count-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(
        string id,
        string title,
        string declaration,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula StepFormula() =>
        Disp(Equal(F.Id("Step"),
            Seq(Call("Fin", D(3)), Sp, Times, Sp, BoolType())));

    private static Formula PathFormula()
    {
        var k = F.Id("k");
        return Disp(Universal("k", Naturals(), Equal(
            Call("Path", k), new Formula.TypeArrow(Call("Fin", k), F.Id("Step")))));
    }

    private static Formula PartialSumFormula()
    {
        var k = F.Id("k");
        var path = F.Id("P");
        var r = F.Id("r");
        var c = F.Id("c");
        var i = F.Id("i");
        var step = new Formula.Apply(path, [i]);
        var selected = And(
            LessThan(Call("val", i), r),
            Equal(Call("fst", step), c));
        var signed = Call("ite", Call("snd", step), D(1), new Formula.Negate(D(1)));
        var summand = Call("ite", selected, signed, D(0));
        var sum = Seq(new Formula.Subscript(Sum,
            Seq(i, Colon, Sp, Call("Fin", k))), Sp, summand);
        var lambda = Parenthesized(Seq(
            LambdaLower, Sp, c, Colon, Sp, Call("Fin", D(3)), Sp, Mapsto, Sp, sum));
        return Disp(Universal("k", Naturals(),
            Universal("P", Call("Path", k),
                Universal("r", Naturals(),
                    Equal(Call("partialSum", path, r), lambda)))));
    }

    private static Formula InCThreePlusFormula()
    {
        var k = F.Id("k");
        var path = F.Id("P");
        var r = F.Id("r");
        var prefix = Universal("r", Call("Fin", Add(k, D(1))), Implies(
            LessThan(D(0), Call("val", r)),
            LessThanOrEqual(D(0), Call("partialSum", path, Call("val", r), D(2)))));
        var finalHeight = Equal(Call("partialSum", path, k, D(2)), D(0));
        return Disp(Universal("k", Naturals(), Universal("P", Call("Path", k), Iff(
            Call("InCThreePlus", path), And(prefix, finalHeight)))));
    }

    private static Formula PlaneFormula(string predicate, int coordinate)
    {
        var k = F.Id("k");
        var path = F.Id("P");
        var r = F.Id("r");
        var containment = Universal("r", Call("Fin", Add(k, D(1))), Implies(
            LessThan(D(0), Call("val", r)),
            Equal(Call("partialSum", path, Call("val", r), D((byte)coordinate)), D(0))));
        return Disp(Universal("k", Naturals(), Universal("P", Call("Path", k), Iff(
            Call(predicate, path), containment))));
    }

    private static Formula DecidablePredicateFormula(string predicate)
    {
        var k = F.Id("k");
        var path = F.Id("P");
        var specialized = Parenthesized(Seq(
            LambdaLower, Sp, path, Colon, Sp, Call("Path", k), Sp, Mapsto, Sp,
            Call(predicate, path)));
        return Disp(Universal("k", Naturals(),
            Call("DecidablePred", specialized)));
    }

    private static Formula CountFormula(string count, string planePredicate)
    {
        var k = F.Id("k");
        var path = F.Id("P");
        var selected = Parenthesized(Seq(
            LambdaLower, Sp, path, Colon, Sp, Call("Path", k), Sp, Mapsto, Sp,
            And(Call("InCThreePlus", path), Call(planePredicate, path))));
        var filtered = Call("filter", Call("univ", Call("Path", k)), selected);
        return Disp(Universal("k", Naturals(),
            Equal(Call(count, k), Call("card", filtered))));
    }

    private static Formula FormulaDefinition()
    {
        var k = F.Id("k");
        var i = F.Id("i");
        var range = Call("Icc", D(1), Add(k, D(1)));
        var numerator = Multiply(
            Call("binom", Multiply(D(2), i), i),
            Call("binom", k, Subtract(i, D(1))));
        var summand = Call("NatDiv", numerator, Add(i, D(1)));
        var sum = Seq(new Formula.Subscript(Sum,
            Seq(i, Sp, InMacro, Sp, range)), Sp, summand);
        return Disp(Universal("k", Naturals(), Equal(Call("formula", k), sum)));
    }

    private static Formula ClaimFormula(string claim, string count)
    {
        var k = F.Id("k");
        var statement = Universal("k", Naturals(), Implies(
            LessThanOrEqual(D(1), k),
            Equal(Call(count, k), Call("formula", k))));
        return Disp(Iff(F.Id(claim), statement));
    }

    private static Formula ResultFormula(string claim) =>
        Disp(new Formula.Not(F.Id(claim)));

    private static Formula Universal(string variable, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable),
            domain,
            body);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(
                Parenthesized(clauses[index]), FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula BoolType() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Bool"));
}
