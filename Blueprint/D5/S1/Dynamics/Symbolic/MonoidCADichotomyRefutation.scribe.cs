using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class MonoidCADichotomyRefutationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/MonoidCADichotomyRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/castronuovo2026groupcaentropy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Boolean OR automaton refutes the finite-monoid entropy dichotomy.",
        H("The entropy dichotomy fails for finite-monoid cellular automata"),
        Blocks(
            Describe.Lean(DescribeId.Create("claim"), DeclarationHandle.Create(Owner + "claim"),
                H("The finite-monoid extension of Theorem 6"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([.. ClaimLines()]))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Castronuovo, Dennunzio, Kari and Margara ask in arXiv:2611.16746v1, §9, "
                        + "second research direction, printed p. 32. “It would be interesting to understand "
                        + "whether the dichotomy extends to cellular automata over finite monoids, and more "
                        + "generally which algebraic constraints force it.” The proposition formalizes the "
                        + "first clause and retains both alternatives of Theorem 6 (p. 21).")),
                    Paragraph(Text(
                        "A ranges over Type with Fintype and Monoid instances. The alphabet carries "
                        + "the discrete uniformity, the bottom UniformSpace instance, and the configuration "
                        + "space carries the product uniformity, denoted by 𝒰. The domain contains every function from "
                        + "Fin D → ℤ to A. The bundled MonoidHom preserves pointwise multiplication and "
                        + "the constant-one configuration. A finite set W supplies the offsets, and "
                        + "localMap reads rule on the translated window. Shift uses z ↦ z + u. "
                        + "Continuity and commutation with every shift are stated separately.")),
                    Paragraph(Text(
                        "For each natural radius r, the source distance is strictly below 2⁻ʳ exactly "
                        + "when the two configurations agree on the centered box [−r,r] in each "
                        + "coordinate. The boxes contain every finite window at some radius, so their "
                        + "agreement relations are cofinal entourages. This identifies uniform "
                        + "equicontinuity of the natural iterates and sensitivity with the source "
                        + "quantifiers, including the strict input bound and the weak separation bound. "
                        + "The time index starts at zero.")),
                    Paragraph(Text(
                        "At a box scale and time length n, the dynamical entourage is equality of "
                        + "box traces at times 0 through n − 1. A minimum spanning cover takes one "
                        + "representative per realized trace. A maximum separated set also takes one "
                        + "per trace, using the source's weak separation inequality at the same scale. "
                        + "Taking the normalized logarithmic upper limits and the supremum over the "
                        + "cofinal box scales identifies coverEntropy on Set.univ with the source "
                        + "entropy. A source trace that ends at time t has length n = t + 1. "
                        + "The infinite value in the display is Top.top in EReal."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Owner + "result"),
                H("The Boolean OR counterexample"),
                StatementSource.FromAuthor(Disp(ExpandedNegation())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The Lean theorem has the literal type ¬ claim. Take D = 2 and Bool with "
                        + "Bool.or as multiplication and false as its unit. At z the map takes the "
                        + "OR of x(z), x(z + e₁) and x(z + e₂). The local lift is continuous, commutes "
                        + "with every shift, and preserves the unit and multiplication. Each of e₁ "
                        + "and e₂ is essential. Flipping the corresponding site alone in the all-false "
                        + "configuration changes the output at the origin.")),
                    Paragraph(Text(
                        "For any input box of radius r, a single true at (r + 1)e₁ agrees with the "
                        + "all-false configuration throughout that box. It reaches the origin after "
                        + "r + 1 steps, while the all-false configuration stays fixed. This contradicts "
                        + "equicontinuity. Independently, true persists at each site, and the all-true "
                        + "configuration is fixed. Agreement with it on any fixed box therefore "
                        + "persists at every time, which rules out sensitivity.")),
                    Paragraph(Text(
                        "In a trace of length n each Boolean coordinate has at most one transition "
                        + "from false to true. Its first true time, with n for a trace that stays false, "
                        + "gives at most n + 1 choices. The number of traces on W is at most "
                        + "(n + 1) to the power |W|. Its normalized logarithm goes to zero for each "
                        + "fixed W. The cover-entropy supremum over boxes is zero. Propagation excludes "
                        + "the equicontinuous alternative, and zero entropy excludes the infinite-entropy "
                        + "alternative. Zero entropy and the same failure of equicontinuity also "
                        + "contradict the zero-entropy entry of Table 2 (p. 31). The possible finite "
                        + "positive entropy values and the classification of algebraic constraints "
                        + "remain open here."))),
                DescribeRole.Theorem)
        )));

    private static Formula V(string name) => F.Id(name);
    private static Formula Op(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Apply(string name, params Formula[] args)
    {
        var items = new List<Formula> { Op(name) };
        foreach (var arg in args)
            items.AddRange([Sp, arg]);
        return Seq([.. items]);
    }

    private static Formula Parenthesized(Formula value, bool scalable = false) =>
        scalable ? Seq(Left, Open, value, Right, Close) : Seq(Open, value, Close);
    private static Formula Arrow(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula For(string variable, Formula type) =>
        Seq(Forall, Sp, V(variable), Colon, Sp, type, Comma);
    private static Formula Some(string variable, Formula type) =>
        Seq(Exists, Sp, V(variable), Colon, Sp, type, Comma);
    private static Formula Inst(string name) =>
        Seq(OpenBracket, Apply(name, V("A")), CloseBracket);
    private static Formula Type => V("Type");
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Lattice =>
        Parenthesized(Arrow(Apply("Fin", V("D")), Seq(Mathbb, Grp(V("Z")))));
    private static Formula FullShift => Parenthesized(Arrow(Lattice, V("A")));
    private static Formula Entropy => Apply("coverEntropy", V("F"), Seq(Op("Set"), Dot, Op("univ")));
    private static Formula Iterate => Seq(V("F"), Caret, Grp(OpenBracket, V("k"), CloseBracket));
    private static Formula EqCont => Apply("UniformEquicontinuous", Parenthesized(Seq(Op("fun"), Sp,
        V("k"), Colon, Sp, Nat, Sp, Mapsto, Sp, Iterate)));
    private static Formula EntourageBinder(Formula quantifier, string name) =>
        Seq(quantifier, Sp, V(name), Sp, InMacro, Sp, Mathcal, Grp(V("U")), Sp, FullShift, Comma);
    private static Formula InEntourage(Formula x, Formula y, string name) =>
        Seq(Parenthesized(Seq(x, Comma, Sp, y)), Sp, InMacro, Sp, V(name));
    private static Formula Sensitivity => Parenthesized(Seq(
        EntourageBinder(Exists, "U"), Sp, For("x", FullShift), Sp, EntourageBinder(Forall, "V"), Sp,
        Some("y", FullShift), Sp, Some("k", Nat), Sp,
        InEntourage(V("x"), V("y"), "V"), Sp, Land, Sp, Neg, Sp,
        Parenthesized(InEntourage(Seq(Iterate, Sp, V("x")), Seq(Iterate, Sp, V("y")), "U"))));

    private static Formula[] ClaimLines() =>
    [
        Seq(For("D", Nat), Sp, D(2), Sp, Le, Sp, V("D"), Sp, Rightarrow, Sp,
            For("A", Type), Sp, Inst("Fintype"), Sp, Inst("Monoid"), Comma),
        Seq(Op("letI"), Sp, Colon, Sp, Apply("UniformSpace", V("A")), Sp, Colon, Eq, Sp, Perp, Semi),
        Seq(For("F", Seq(FullShift, Sp, To, Caret, Grp(Star), Sp, FullShift))),
        Seq(Parenthesized(Seq(Some("W", Apply("Finset", Lattice)), Sp,
            Some("rule", Arrow(Parenthesized(Arrow(V("W"), V("A"))), V("A"))), Sp,
            V("F"), Sp, Eq, Sp, Apply("localMap", V("W"), V("rule")))), Sp, Rightarrow),
        Seq(Apply("Continuous", V("F")), Sp, Rightarrow),
        Seq(Parenthesized(Seq(For("u", Lattice), Sp, For("x", FullShift), Sp,
            V("F"), Sp, Parenthesized(Apply("shift", V("u"), V("x"))), Sp, Eq, Sp,
            Apply("shift", V("u"), Parenthesized(Seq(V("F"), Sp, V("x")))))), Sp, Rightarrow),
        Seq(Parenthesized(Seq(EqCont, Sp, Land, Sp, Entropy, Sp, Eq, Sp, D(0))), Sp, Lor),
        Parenthesized(Seq(Sensitivity, Sp, Land, Sp, Entropy, Sp, Eq, Sp, Infty))
    ];

    private static Formula ExpandedNegation() =>
        Seq(Neg, Sp, Parenthesized(new Formula.Aligned([.. ClaimLines()]), scalable: true));
}
