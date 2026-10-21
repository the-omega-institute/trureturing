using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class BahturinCentronePereiraPeakGroupsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/bahturincentronepereira2026peak");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The constructed finite peak group is neither solvable nor a Frobenius group.",
        H("Refutation of the peak-group dichotomy"),
        Blocks(
            Definition("degreeSet", "Complex character degrees", DegreeSet(),
                "The set consists of the dimensions of simple finite-dimensional complex representations.", true),
            Definition("IsPeak", "Peak groups", Peak(),
                "A peak group has a character degree divisible by every character degree.", true),
            Definition("IsFrobeniusWithComplement", "Frobenius complements", Frobenius(),
                "A complement is a nontrivial proper subgroup with trivial intersection with each conjugate by an element outside it.", true),
            Definition("fitting", "The Fitting subgroup", Fitting(),
                "The Fitting subgroup is the supremum of the normal nilpotent subgroups.", false),
            Node("fitting_normal", "Normality of the Fitting subgroup", NormalFitting(),
                "A supremum of normal subgroups is normal.", DescribeRole.Theorem, false),
            Definition("HasAllowedOrder", "Excluded prime divisors", AllowedOrder(),
                "The order is divisible by none of two, three, and five.", true),
            Definition("ComplementCondition", "Structure of the quotient of a complement", Complement(),
                "The quotient by the Fitting subgroup contains a normal subgroup isomorphic to the product of SL(2, ZMod 5) and a group with cyclic Sylow subgroups and the specified prime exclusions. MulEquiv is the type of multiplicative equivalences.", true),
            Definition("AlternativeTwo", "The Frobenius alternative", Alternative(),
                "The group has a Frobenius complement satisfying the quotient condition.", true),
            Definition("claim", "Conjecture 31", Equal(X("claim"), Parenthesized(ClaimBody())),
                "For every finite peak group, exactly one of solvability and the Frobenius alternative holds.", true),
            Node("result", "The conjecture is false", new Formula.Not(Parenthesized(ClaimBody())),
                "The additive group of (ZMod 11) squared admits the displayed fixed-point-free SL(2, ZMod 5) action. Its semidirect product has a simple representation of dimension 120 and every simple degree divides 120. An abelian direct factor of order two preserves these degrees. The SL(2, ZMod 5) quotient prevents solvability, while the central element from the direct factor prevents every Frobenius complement.", DescribeRole.Theorem, false))));

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose, bool literature) =>
        Node(name, title, formula, prose, DescribeRole.Definition, literature);
    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role, bool literature,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("bcp31-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula DegreeSet()
    {
        Formula g = F.Id("G"), d = F.Id("d"), v = F.Id("V");
        Formula body = ExistsIn("V", Call("FDRep", Complex(), g),
            And(Call(Q("CategoryTheory", "Simple"), v), Equal(Call(Q("Module", "finrank"), Complex(), v), d)));
        return Group("G", false, Equal(Call(X("degreeSet"), g),
            SetBuilder("d", Nat(), body)));
    }
    private static Formula Peak()
    {
        Formula g = F.Id("G"), d = F.Id("d"), e = F.Id("e");
        Formula body = ExistsIn("d", Nat(), And(Member(d, Call(X("degreeSet"), g)),
            All("e", Nat(), Imp(Member(e, Call(X("degreeSet"), g)), Divides(e, d)))));
        return Group("G", false, Equal(Call(X("IsPeak"), g), Parenthesized(body)));
    }
    private static Formula Frobenius()
    {
        Formula g = F.Id("G"), h = F.Id("H"), x = F.Id("g");
        Formula body = And(Ne(h, Q("Bot", "bot")), And(Ne(h, Q("Top", "top")),
            All("g", g, Imp(new Formula.Not(Member(x, h)),
                Equal(Call(Q("Min", "min"), h,
                    Call(Q("Subgroup", "map"), Call(Q("MulAut", "conj"), x), h)), Q("Bot", "bot"))))));
        return Group("G", false, All("H", Call("Subgroup", g),
            Equal(Call(X("IsFrobeniusWithComplement"), g, h), Parenthesized(body))));
    }
    private static Formula Fitting()
    {
        Formula h = F.Id("H"), n = F.Id("N");
        return Group("H", true, Equal(Call(X("fitting"), h),
            Call("sSup", SetBuilder("N", Call("Subgroup", h),
                And(Call(Q("Subgroup", "Normal"), n), Call(Q("Group", "IsNilpotent"), n))))));
    }
    private static Formula NormalFitting() => Group("H", true,
        Call(Q("Subgroup", "Normal"), Call(X("fitting"), F.Id("H"))));
    private static Formula AllowedOrder()
    {
        Formula t = F.Id("T");
        return All("T", Type(), Equal(Call(X("HasAllowedOrder"), t), Parenthesized(
            And(new Formula.Not(Divides(D(2), Call(Q("Nat", "card"), t))),
                And(new Formula.Not(Divides(D(3), Call(Q("Nat", "card"), t))),
                    new Formula.Not(Divides(D(5), Call(Q("Nat", "card"), t))))))));
    }
    private static Formula Complement()
    {
        Formula h = F.Id("H"), hzero = F.Id("Hzero"), t = F.Id("T"), p = F.Id("p"), sylow = F.Id("P");
        Formula quotient = Seq(h, Sp, Slash, Sp, Call(X("fitting"), h));
        Formula special = Call(Q("Matrix", "SpecialLinearGroup"), Call("Fin", D(2)), Call("ZMod", D(5)));
        Formula cyclic = All("p", Nat(), Instance(Call("Fact", Call(Q("Nat", "Prime"), p)),
            All("P", Call("Sylow", p, t), Call("IsCyclic", sylow))));
        Formula product = Parenthesized(Seq(special, Sp, Times, Sp, t));
        Formula factors = And(Call("Nonempty", Call("MulEquiv", hzero, product)), And(cyclic, Call(X("HasAllowedOrder"), t)));
        Formula body = ExistsIn("Hzero", Call("Subgroup", Parenthesized(quotient)),
            And(Call(Q("Subgroup", "Normal"), hzero),
                ExistsIn("T", Type(), InstanceExists(Call("Group", t),
                    InstanceExists(Call("Finite", t), factors)))));
        return Group("H", true, Equal(Call(X("ComplementCondition"), h), Parenthesized(body)));
    }
    private static Formula Alternative()
    {
        Formula g = F.Id("G"), h = F.Id("H");
        return Group("G", true, Equal(Call(X("AlternativeTwo"), g), Parenthesized(
            ExistsIn("H", Call("Subgroup", g),
                And(Call(X("IsFrobeniusWithComplement"), g, h), Call(X("ComplementCondition"), h))))));
    }
    private static Formula ClaimBody()
    {
        Formula g = F.Id("G"), soluble = Call(Q("Group", "IsSolvable"), g), alternative = Call(X("AlternativeTwo"), g);
        return Group("G", true, Imp(Call(X("IsPeak"), g),
            And(Or(soluble, alternative), new Formula.Not(Parenthesized(And(soluble, alternative))))));
    }
    private static Formula Group(string name, bool finite, Formula body)
    {
        Formula v = F.Id(name);
        return All(name, Type(), Instance(Call("Group", v),
            finite ? Instance(Call("Finite", v), body) : body));
    }
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula InstanceExists(Formula type, Formula body) => Seq(Exists, Sp, OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Type() => F.Id("Type");
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula X(string name) => Q("D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31", name);
    private static Formula Q(string owner, string name)
    {
        Formula[] pieces = (owner + "." + name).Split('.').SelectMany((part, index) =>
            index == 0 ? new Formula[] { Operatorname, Grp(F.Id(part)) }
                : new Formula[] { Dot, Operatorname, Grp(F.Id(part)) }).ToArray();
        return Seq(pieces);
    }
    private static Formula Call(string name, params Formula[] args) => Call(F.Id(name), args);
    private static Formula Call(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsIn(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula SetBuilder(string name, Formula type, Formula body) =>
        Seq(OpenBrace, F.Id(name), Colon, Sp, type, Sp, Bar, Sp, Parenthesized(body), CloseBrace);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Divides(Formula a, Formula b) => Seq(a, Sp, Mid, Sp, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
}
