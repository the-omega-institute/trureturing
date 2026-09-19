using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class CenteredReducedResidueProgressionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithUnits/CenteredReducedResidueProgressions.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/phothila2026centered");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The longest positive-step progression in a short centered squarefree reduced residue system has the conjectured length.",
        H("Centered Reduced Residue Progressions"),
        Blocks(
            Node("centered-reduced-residue", "CenteredReducedResidue",
                "The fixed centered reduced residue system", CenteredFormula(),
                "For a natural modulus n, the centered system consists of the integers in the source interval beginning at minus (n+1)/2 plus one and ending n-1 steps later, subject to gcd one with n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("admissible-progression-length", "AdmissibleLength",
                "Positive-step progression lengths", AdmissibleFormula(),
                "A natural length s is admissible when some integer start and positive natural step place all terms with indices below s in the fixed centered reduced residue system.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("greatest-prime-factor", "GreatestPrimeFactor",
                "The greatest prime factor", GreatestPrimeFormula(),
                "The greatest prime factor is the supremum of the finite set of prime factors. On the theorem's domain that set is nonempty.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("centered-progression-maximum", "result",
                "The exact maximum progression length", ResultFormula(),
                "Let p be the greatest prime factor of n, d=n/p, and k=p-1-floor(2p/d), where the inner floor is natural Euclidean division. For every even squarefree n with at least three distinct prime factors and d<2p, k is an admitted length and bounds every admitted length. The rational floor of p-2p/d is exactly the same natural number k.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula CenteredFormula()
    {
        Formula n = F.Id("n"), x = F.Id("x");
        Formula c = Call("NatDiv", Add(n, D(1)), D(2));
        Formula lower = Add(new Formula.Negate(c), D(1));
        Formula upper = Add(lower, Sub(n, D(1)));
        return Universal([Bound("n", Naturals()), Bound("x", Integers())],
            Iff(Call("CenteredReducedResidue", n, x),
                And(LessEqual(lower, x), LessEqual(x, upper),
                    Equal(Call("gcd", x, n), D(1)))));
    }

    private static Formula AdmissibleFormula()
    {
        Formula n = F.Id("n"), s = F.Id("s"), a = F.Id("a"), h = F.Id("h"), i = F.Id("i");
        Formula term = Add(a, Mul(i, h));
        Formula terms = Universal([Bound("i", Naturals())],
            Implies(Less(i, s), Call("CenteredReducedResidue", n, term)));
        Formula witness = Existential([Bound("a", Integers()), Bound("h", Naturals())],
            And(Less(D(0), h), terms));
        return Universal([Bound("n", Naturals()), Bound("s", Naturals())],
            Iff(Call("AdmissibleLength", n, s), witness));
    }

    private static Formula GreatestPrimeFormula()
    {
        Formula n = F.Id("n");
        return Universal([Bound("n", Naturals())],
            Equal(Call("GreatestPrimeFactor", n), Call("sup", Call("primeFactors", n))));
    }

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n"), s = F.Id("s"), p = F.Id("p"), d = F.Id("d"), k = F.Id("k");
        Formula hypotheses = And(Call("Even", n), Call("Squarefree", n),
            LessEqual(D(3), Call("card", Call("primeFactors", n))), Less(d, Mul(D(2), p)));
        Formula admissibleSet = Seq(OpenBrace, s, Sp, InMacro, Sp, Naturals(), Sp, Mid, Sp,
            Call("AdmissibleLength", n, s), CloseBrace);
        Formula maximum = Call("IsGreatest", admissibleSet, k);
        Formula rationalFloor = Equal(
            Seq(Lfloor, Sp, Sub(p, new Formula.Fraction(Mul(D(2), p), d)), Rfloor), k);
        return Universal([Bound("n", Naturals())], Seq(
            Let(p, Call("GreatestPrimeFactor", n)),
            Let(d, Call("NatDiv", n, p)),
            Implies(hypotheses, Seq(
                Let(k, Sub(Sub(p, D(1)), Call("NatDiv", Mul(D(2), p), d))),
                And(maximum, rationalFloor)))));
    }

    private static Formula Let(Formula name, Formula value) => Seq(
        Operatorname, Grp(F.Id("let")), Sp, name, Sp, Eq, Sp, value, Semi, Sp);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Universal(Formula.BoundVariable[] bounds, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. bounds], body);

    private static Formula Existential(Formula.BoundVariable[] bounds, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. bounds], body);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LessEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(params Formula[] clauses) => clauses.Aggregate(
        (a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
}
