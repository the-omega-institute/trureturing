using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GroupWords;

internal sealed class NathansonProblem9Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/GroupWords/NathansonProblem9.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/nathanson2026sumintersections");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every infinite group admits a decreasing sequence with a nontrivial proper product intersection spectrum.",
        H("Nontrivial product intersection spectra"),
        Blocks(
            Node("ASD", "Asymptotically strict decrease", DecreaseFormula(),
                "Nathanson, Section 2, calls a sequence decreasing when every next set is contained in its predecessor, and asymptotically strictly decreasing when adjacent sets differ at infinitely many indices. The index type PNat is the positive integers. The common intersection may be empty.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("spectrum", "The full positive spectrum", SpectrumFormula(),
                "Section 1 defines the spectrum using equality between the power of the common intersection and the intersection of the powers. The natural exponent is restricted to be positive. Mathlib pointwise set powers are all ordered products of that many factors, with repetitions allowed. Multiplication need not commute.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("nathanson-nine-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Existence in every infinite group"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Problem 9 asks: “Let G be an infinite torsion group. Describe the product intersection sets H_Q(G). Must there exist X in H_N^*(G) with X != {1} and X != N?” The theorem answers the final existence question affirmatively. Set X equal to spectrum A; ASD A places X in H_N^*(G). The theorem applies to every infinite group, so the torsion hypothesis is unnecessary. G is arbitrary in cardinality and need not be abelian or have bounded exponent. The preceding classification request remains a separate question.")),
                    Paragraph(Text("If the range of cubes is finite, an infinite common-cube fibre has injective squares: equality of squares together with equality of cubes cancels to equality of roots. Thin both ordered mixed pair products, and use singleton tails. Their common intersection and square-product intersection are empty, while the common cube lies in every cube-product set. Thus 2 belongs to the full spectrum and 3 does not.")),
                    Paragraph(Text("If the range of cubes is infinite, recursively choose cubes outside all earlier cube inverse-orbits. The corresponding roots have pairwise disjoint inverse-pairs. Thin every signed mixed triple support. Pure signed triples take one of the four values x^3, x, inverse x, inverse(x^3), each of which eventually avoids any fixed group element. The inverse-pair tails have empty common intersection and empty cube-product intersection, while the identity belongs to every square-product set. Thus 3 belongs to the full spectrum and 2 does not.")),
                    Paragraph(Text("The thinning uses Yann Pequignot's relativized all-arity infinite_ramsey at revision b63066fd9f8075a30bc78d392405426bf084e226. Its exists_infinite_fiber_nat supplies the final colour pigeonhole, and its Set.Infinite.exists_strictMono supplies increasing support enumeration. The compatible proof is preserved under Apache-2.0 with its complete license and attribution. A recursively chosen increasing diagonal handles countably many requirements. Only the initial word-evaluation range is countable; no countability assumption on G enters the argument.")),
                    Paragraph(Text("The repository and its pinned Mathlib were searched for product-intersection spectra, infinite Ramsey thinning, cube ranges and the exact Nathanson question. The existing Problem 12 result concerns integer-additive affine invariance and supplies no group-existence theorem. At Mathlib revision 56a005855ea17e0b0958f73ec801ae140b0a1679, Finite.exists_infinite_fiber gives the common-cube fibre; Set.countable_range and countable_iff_exists_surjective enumerate the requirements; Nat.nth_strictMono and Nat.nth_mem_of_infinite enumerate infinite supports; Finset.orderEmbOfFin_unique identifies their increasing finite enumerations. Group cancellation and pointwise set powers supply the algebraic interfaces. The cited Ramsey source supplies the missing relativized all-arity theorem. The literature boundary is the bounded primary-source and prior-solution screen in the accompanying source note; no worldwide priority assertion follows."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("nathanson-2026-problem9-torsion-nontrivial-spectrum-existence"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("nathanson-nine-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => Apply(Named(name), args);
    private static Formula Apply(Formula function, params Formula[] args) =>
        args.Length == 0 ? function : new Formula.Apply(function, [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        Apply(Seq(Named(owner), Dot, Named(name)), args);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Par(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Instance(string name, Formula type, Formula body) =>
        Seq(OpenBracket, Call(name, type), CloseBracket, Comma, Sp, body);
    private static Formula Fun(string name, Formula type, Formula body) =>
        Seq(Named("fun"), Sp, Par(Seq(F.Id(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Par(left), FormulaLogicOperator.And, Par(right));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula PNat() => new Formula.Power(Nat(), Plus);
    private static Formula Family() => new Formula.TypeArrow(PNat(), Call("Set", F.Id("G")));
    private static Formula SetOf(string name, Formula type, Formula body) =>
        Seq(OpenBrace, F.Id(name), Sp, Colon, Sp, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula Inter(Formula body) => Qualified("Set", "iInter", Fun("q", PNat(), body));
    private static Formula Positive() => SetOf("h", Nat(),
        new Formula.Relation(D(0), FormulaRelationOperator.LessThan, F.Id("h")));
    private static Formula OneSet() => Seq(OpenBrace, D(1), CloseBrace);

    private static Formula DecreaseFormula()
    {
        var a = F.Id("A"); var q = F.Id("q");
        var next = Apply(a, new Formula.Binary(q, FormulaBinaryOperator.Add, D(1)));
        var current = Apply(a, q);
        var dec = All("q", PNat(), new Formula.Relation(next, FormulaRelationOperator.SubsetOf, current));
        var strict = Qualified("Set", "Infinite", SetOf("q", PNat(), Ne(current, next)));
        return Disp(All("G", Named("Type"), All("A", Family(),
            Eq(Call("ASD", a), Par(And(dec, strict))))));
    }

    private static Formula SpectrumFormula()
    {
        var a = F.Id("A"); var h = F.Id("h"); var aq = Apply(a, F.Id("q"));
        var body = And(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, h),
            Eq(new Formula.Power(Par(Inter(aq)), h), Inter(new Formula.Power(Par(aq), h))));
        return Disp(All("G", Named("Type"), Instance("Group", F.Id("G"), All("A", Family(),
            Eq(Call("spectrum", a), SetOf("h", Nat(), body))))));
    }

    private static Formula ResultFormula()
    {
        var a = F.Id("A");
        var body = And(Call("ASD", a), And(Ne(Call("spectrum", a), OneSet()), Ne(Call("spectrum", a), Positive())));
        return Disp(All("G", Named("Type"), Instance("Group", F.Id("G"),
            Instance("Infinite", F.Id("G"), Ex("A", Family(), body)))));
    }
}
