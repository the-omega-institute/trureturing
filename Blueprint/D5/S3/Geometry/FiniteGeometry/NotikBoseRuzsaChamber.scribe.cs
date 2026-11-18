using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.FiniteGeometry;

internal sealed class NotikBoseRuzsaChamberDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FiniteGeometry/notik2026singergolomb");
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Type => Named("Type");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Apply(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Imp(Formula lhs, Formula rhs) => Seq(lhs, Sp, Implies, Sp, rhs);
    private static Formula And(Formula lhs, Formula rhs) => Seq(Par(lhs), Sp, Land, Sp, Par(rhs));
    private static Formula All(Formula v, Formula t, Formula body) =>
        Seq(Forall, Sp, v, Colon, Sp, t, Comma, Sp, body);
    private static Formula Some(Formula v, Formula t, Formula body) =>
        Seq(Exists, Sp, v, Colon, Sp, t, Comma, Sp, body);
    private static Formula Instance(string name, params Formula[] args) =>
        Seq(OpenBracket, Call(name, args), CloseBracket, Sp);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Label(Formula n) => Call("Label", n);
    private static Formula Gaps(Formula n, Formula t) => new Formula.TypeArrow(Fin(n), t);
    private static Formula MinusOne(Formula n) => Seq(n, Minus, D(1));
    private static Formula Mod(Formula x, Formula n) => Call("mod", x, n);
    private static Formula Val(Formula f) => Seq(f, Dot, Named("val"));
    private static Formula Cast(Formula f, Formula t) => Par(Seq(f, Colon, Sp, t));
    private static Formula FieldTypes(Formula f, Formula k, Formula body) =>
        All(f, Type, All(k, Type,
            Seq(Instance("Field", f), Instance("Field", k),
                OpenBracket, Alpha, Colon, Sp, Call("Algebra", f, k), CloseBracket, Sp, body)));
    private static Formula BoseResidue(Formula f, Formula k) =>
        new Formula.Subscript(Named("BoseResidue"), Seq(f, Comma, Sp, k, Comma, Sp, Alpha));

    private static Formula LabelFormula()
    {
        var n = F.Id("n"); var i = F.Id("i"); var j = F.Id("j");
        var marks = Fin(Seq(n, Plus, D(1)));
        return All(n, Nat, Seq(Label(n), Eq, OpenBrace, Par(Seq(i, Comma, j)),
            Colon, Sp, marks, Times, Sp, marks, Mid, Sp, i, Lt, j, CloseBrace));
    }

    private static Formula IntervalSumFormula()
    {
        var a = F.Id("A"); var n = F.Id("n"); var g = F.Id("g");
        var i = F.Id("i"); var j = F.Id("j"); var k = F.Id("k");
        var indices = Seq(k, Colon, Sp, Fin(n), Comma, Sp, i, Leq, Sp, Val(k), Lt, j);
        var sum = Seq(new Formula.Subscript(Sum, indices), Apply(g, k));
        return All(a, Type, Seq(Instance("AddCommMonoid", a), All(n, Nat,
            All(g, Gaps(n, a), All(i, Nat, All(j, Nat,
                Seq(Call("intervalSum", g, i, j), Eq, sum)))))));
    }

    private static Formula DistanceFormula()
    {
        var a = F.Id("A"); var n = F.Id("n"); var g = F.Id("g"); var p = F.Id("p");
        var first = new Formula.Subscript(p, D(1));
        var second = new Formula.Subscript(p, D(2));
        return All(a, Type, Seq(Instance("AddCommMonoid", a), All(n, Nat,
            All(g, Gaps(n, a), All(p, Label(n), Seq(Call("distance", g, p), Eq,
                Call("intervalSum", g, Val(first), Val(second))))))));
    }

    private static Formula ChamberOrderFormula()
    {
        var a = F.Id("A"); var n = F.Id("n"); var g = F.Id("g"); var x = F.Id("x");
        var p = F.Id("p"); var q = F.Id("q");
        var gp = Call("distance", g, p); var gq = Call("distance", g, q);
        var xp = Call("distance", x, p); var xq = Call("distance", x, q);
        var labels = Label(n);
        var distinct = All(p, labels, All(q, labels, Imp(Seq(gp, Eq, gq), Seq(p, Eq, q))));
        var positive = All(p, labels, Seq(D(1), Leq, Sp, xp));
        var separate = All(p, labels, All(q, labels,
            Imp(Seq(gp, Lt, gq), Seq(xp, Plus, D(1), Leq, Sp, xq))));
        return All(a, Type, Seq(Instance("AddCommMonoid", a), Instance("One", a), Instance("LE", a),
            All(n, Nat, All(g, Gaps(n, Nat), All(x, Gaps(n, a),
                Seq(Call("ChamberOrder", g, x), Iff, Sp, And(distinct, And(positive, separate))))))));
    }

    private static Formula UniqueShortestFormula()
    {
        var n = F.Id("n"); var g = F.Id("g"); var x = F.Id("x"); var i = F.Id("i");
        var realGaps = Par(Seq(i, Mapsto, Sp, Cast(Apply(g, i), Real)));
        var referenceLength = Cast(Call("intervalSum", g, D(0), n), Real);
        var referenceChamber = Call("ChamberOrder", g, realGaps);
        var shortest = All(x, Gaps(n, Real), Imp(Call("ChamberOrder", g, x),
            Imp(Seq(Call("intervalSum", x, D(0), n), Leq, Sp, referenceLength), Seq(x, Eq, realGaps))));
        return All(n, Nat, All(g, Gaps(n, Nat),
            Seq(Call("UniqueShortest", g), Iff, Sp, And(referenceChamber, shortest))));
    }

    private static Formula LargestGapCutFormula()
    {
        var m = F.Id("M"); var n = F.Id("n"); var s = F.Id("S");
        var start = F.Id("b"); var g = F.Id("g"); var i = F.Id("i"); var r = F.Id("r");
        var length = Call("intervalSum", g, D(0), n);
        var positive = All(i, Fin(n), Seq(D(0), Lt, Apply(g, i)));
        var largest = All(i, Fin(n), Seq(Apply(g, i), Leq, Sp, m, Minus, length));
        var offset = Call("intervalSum", g, D(0), Val(i));
        var residues = All(r, Fin(m), Seq(Apply(s, r), Iff, Sp,
            Some(i, Fin(Seq(n, Plus, D(1))), Seq(Val(r), Eq, Mod(Seq(Val(start), Plus, offset), m)))));
        var body = And(positive, And(Seq(length, Lt, m), And(largest, residues)));
        return All(m, Nat, All(n, Nat, All(s, new Formula.TypeArrow(Fin(m), Named("Prop")),
            All(start, Fin(m), All(g, Gaps(n, Nat),
                Seq(Call("LargestGapCut", s, start, g), Iff, Sp, body))))));
    }

    private static Formula BoseResidueFormula()
    {
        var f = F.Id("F"); var k = F.Id("K"); var m = F.Id("M"); var theta = Theta;
        var u = F.Id("u"); var r = F.Id("r"); var e = F.Id("e"); var a = F.Id("a");
        var onLine = Some(a, f, Seq(new Formula.Power(theta, Val(e)), Eq, theta, Plus,
            Call("algebraMap", f, k, a)));
        var exponent = Some(e, Fin(m), And(Seq(Val(r), Eq, Mod(Seq(u, Cdot, Sp, Val(e)), m)), onLine));
        return FieldTypes(f, k, All(m, Nat, All(theta, k, All(u, Nat, All(r, Fin(m),
            Seq(Apply(BoseResidue(f, k), theta, u, r), Iff, Sp, exponent))))));
    }

    private static Formula RuzsaResidueFormula()
    {
        var p = F.Id("p"); var h = F.Id("h"); var u = F.Id("u"); var r = F.Id("r");
        var s = F.Id("s"); var i = F.Id("i"); var field = Call("ZMod", p);
        var m = Seq(p, Cdot, Sp, Par(MinusOne(p)));
        var scaled = Seq(Val(r), Eq, Mod(Seq(u, Cdot, Sp, Val(s)), m));
        var first = Seq(Mod(Val(s), MinusOne(p)), Eq, Val(i));
        var second = Seq(Cast(Val(s), field), Eq, new Formula.Power(h, Val(i)));
        var crt = Some(s, Fin(m), Some(i, Fin(MinusOne(p)), And(scaled, And(first, second))));
        return All(p, Nat, All(h, field, All(u, Nat, All(r, Fin(m),
            Seq(Call("RuzsaResidue", h, u, r), Iff, Sp, crt)))));
    }

    private static Formula BoseFormula()
    {
        var q = F.Id("q"); var f = F.Id("F"); var k = F.Id("K"); var theta = Theta;
        var u = F.Id("u"); var start = F.Id("b"); var g = F.Id("g");
        var square = new Formula.Power(q, D(2));
        var modulus = MinusOne(square);
        var residues = Par(Apply(BoseResidue(f, k), theta, u));
        var cuts = All(start, Fin(modulus), All(g, Gaps(MinusOne(q), Nat),
            Imp(Call("LargestGapCut", residues, start, g), Call("UniqueShortest", g))));
        var generators = All(theta, k, All(u, Nat,
            Imp(Seq(Call("orderOf", theta), Eq, modulus),
                Imp(Call("Coprime", u, modulus), cuts))));
        var cardinalities = Imp(Seq(Call("card", f), Eq, q),
            Imp(Seq(Call("card", k), Eq, square), generators));
        return Seq(Named("Bose"), Iff, Sp, All(q, Nat,
            FieldTypes(f, k, Seq(Instance("Finite", f), cardinalities))));
    }

    private static Formula RuzsaFormula()
    {
        var p = F.Id("p"); var h = F.Id("h"); var u = F.Id("u");
        var start = F.Id("b"); var g = F.Id("g");
        var modulus = Seq(p, Cdot, Sp, Par(MinusOne(p)));
        var residues = Par(Call("RuzsaResidue", h, u));
        var cuts = All(start, Fin(modulus), All(g, Gaps(Seq(p, Minus, D(2)), Nat),
            Imp(Call("LargestGapCut", residues, start, g), Call("UniqueShortest", g))));
        var roots = All(h, Call("ZMod", p), All(u, Nat,
            Imp(Seq(Call("orderOf", h), Eq, MinusOne(p)), Imp(Call("Coprime", u, modulus), cuts))));
        return Seq(Named("Ruzsa"), Iff, Sp, All(p, Nat, Imp(Call("Prime", p), roots)));
    }

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Definition, bool fromLiterature = false,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Module + "." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            fromLiterature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shorter real rulers refute both of Notik's chamber analogues.",
        H("The Bose and Ruzsa chamber assertions"), Blocks(
            Node("Label", "Increasing pairs of mark indices", LabelFormula(),
                "There are n kept gaps and n + 1 marks."),
            Node("intervalSum", "Interval sum of kept gaps", IntervalSumFormula(),
                "The finite sum includes a gap exactly when its index lies between i inclusive and j exclusive."),
            Node("distance", "Labelled distance", DistanceFormula(),
                "The first and second components of the pair p are the endpoints of the interval."),
            Node("ChamberOrder", "Unit separation in reference order", ChamberOrderFormula(),
                "Distinct labels have distinct reference distances. Every candidate distance is at least one, and the ordered inequalities separate each pair of labelled distances by at least one. The consecutive rows give all these inequalities by adding along the ordered list."),
            Node("UniqueShortest", "Unique shortest point of the chamber", UniqueShortestFormula(),
                "The reference itself lies in the real chamber. Every point of the chamber of at most its total length has the same gap vector."),
            Node("LargestGapCut", "Cut at a largest cyclic gap", LargestGapCutFormula(),
                "Increasing offsets from the starting residue exhaust the cyclic set. Their total length is below the modulus, and the wraparound gap is at least every kept gap."),
            Node("BoseResidue", "Scaled affine-line exponent", BoseResidueFormula(),
                "The map from F to K is the given field embedding. The exponent ranges over the entire cyclic modulus."),
            Node("RuzsaResidue", "Scaled CRT residue", RuzsaResidueFormula(),
                "The cast to ZMod p and the remainder modulo p minus one specify the two congruences of the unscaled residue."),
            Node("Bose", "Bose universal assertion", BoseFormula(),
                "The finite base field has size q, and its extension has size q squared. The multiplicative generator, coprime multiplier, and largest-gap cut are all universally quantified."),
            Node("Ruzsa", "Ruzsa universal assertion", RuzsaFormula(),
                "The prime, primitive root, coprime multiplier, and largest-gap cut are all universally quantified."),
            Node("claim", "The two questions in Section 10",
                Seq(Named("claim"), Iff, Sp, Par(Seq(Named("Bose"), Sp, Lor, Sp, Named("Ruzsa")))),
                "Section 10 asks the two analogues of the Section 7 conjecture. The disjunction asks whether either universal assertion holds.",
                fromLiterature: true),
            Node("result", "Both universal assertions are false",
                Seq(Neg, Sp, Par(Seq(Named("Bose"), Sp, Lor, Sp, Named("Ruzsa")))),
                "For Bose, use the field adjoining a root of X squared plus four over F seven. The generator is one plus that root and has order 48. Multiplication by five gives residues 4, 5, 9, 11, 30, 39, 42. Cutting between 11 and 30 gives gaps (9, 3, 10, 1, 4, 2). The rational gaps (17/2, 3, 19/2, 1, 4, 2) preserve the chamber and shorten the total from 29 to 28. For Ruzsa, the prime is five, the primitive root is two, and the multiplier is one. The residues 3, 14, 16, 17 give the cut between 3 and 14. The gaps (2, 1, 5) lie in the chamber of (2, 1, 6) and shorten the total from 9 to 8. The exact rational inequalities transfer to real gaps.",
                DescribeRole.Theorem,
                resolution: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("notik-bose-ruzsa-chambers"), ResolutionKind.Refuted)))));
}
