using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PrimitiveLifts;

internal sealed class FreeRootAmalgamationDocument : IScribeDocumentDefinition
{
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) =>
        new(FormulaIdentifier.Create(n), t);
    private static Formula Q(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. v], f);
    private static Formula Ex(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. v], f);
    private static Formula And(Formula a, Formula b) => Seq(Open, a, Sp, Land, Sp, b, Close);
    private static Formula Implication(Formula a, Formula b) =>
        Seq(Open, a, Sp, Implies, Sp, b, Close);
    private static Formula Iff(Formula a, Formula b) =>
        Seq(Open, a, Sp, F.Iff, Sp, b, Close);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula FreeGroup() => Call("FreeGroup", I("Bool"));
    private static Formula Root() => And(Equal(I("x"), Pow(I("z"), I("n"))),
        Equal(I("y"), Pow(I("z"), I("m"))));
    private static Formula RootEquation() => Q(
        Implication(Call("Coprime", I("m"), I("n")),
            Iff(Equal(Pow(I("x"), I("m")), Pow(I("y"), I("n"))),
                Ex(And(Root(), Q(Implication(Root(), Equal(I("w"), I("z"))),
                    B("w", FreeGroup()))), B("z", FreeGroup())))),
        B("x", FreeGroup()), B("y", FreeGroup()), B("m", I("Nat")), B("n", I("Nat")));
    private static Formula Qualified(params string[] names)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (items.Count > 0)
                items.Add(Dot);
            items.Add(I(name));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula App(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual free group on Bool is an infinite nonnilpotent sharpness countermodel with unique coprime roots.",
        H("Free-root amalgamation and the infinite sharpness countermodel"), Blocks(
        Describe.Lean(DescribeId.Create("free-group-bool-infinite-nonnilpotent-coprime-root"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FreeRootAmalgamation.freeGroupBool_infinite_not_nilpotent_coprime_root"),
            H("Exact FreeGroup Bool countermodel"),
            StatementSource.FromAuthor(Disp(And(
                And(Call("Infinite", FreeGroup()),
                    new Formula.Not(App(Qualified("Group", "IsNilpotent"), FreeGroup()))),
                RootEquation()))),
            AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("For the actual group FreeGroup Bool, infinitude, failure of nilpotence, and the full coprime-power root equivalence hold in one conjunction. For every x,y and every natural m,n with m.Coprime n, x^m=y^n if and only if there exists exactly one z with x=z^n and y=z^m. The statement retains both zero-exponent boundaries: coprimality turns m=0 into n=1 (and symmetrically in the displayed equivalence), so no positivity hypothesis has been added.")),
                Paragraph(Text("The root proof first uses Mathlib's HasUniqueRoots instance for FreeGroup. Conjugating x by y and applying conj_pow transports the equality of mth powers to the conjugate; when m is nonzero, power injectivity gives y*x*y⁻¹=x and hence Commute x y. When m=0, the coprimality boundary gives n=1 and the equality gives y=1 directly. The commuting pair is placed in H=Subgroup.closure {x,y}; Subgroup.isMulCommutative_closure supplies the pinned commutative instance, and the existing repository theorem NilpotentRootAmalgamation.pow_eq_pow_iff_exists_unique is applied to H. Its witness is transported back to FreeGroup, while ambient uniqueness uses the nonzero m power map; the m=0 branch is handled explicitly. The reverse implication is the general identity (z^n)^m=(z^m)^n.")),
                Paragraph(Text("The same explicit quotient q:FreeGroup Bool→DihedralGroup 0 sends false to r(1) and true to sr(0). Every rotation r(i) is q((of false)^(ZMod.cast i)) and every reflection sr(i) is q(of true*(of false)^(ZMod.cast i)), using r_one_zpow and sr_mul_r; therefore q is surjective. Infinite.of_surjective transfers infinitude from DihedralGroup 0. If FreeGroup Bool were nilpotent, Group.nilpotent_of_surjective would make DihedralGroup 0 nilpotent, while center_ne_bot contradicts DihedralGroup.center_eq_bot_of_zero. Thus this quotient proves both countermodel properties in one construction.")),
                Paragraph(Text("The finite Sylow converse has a separate boundary. In a finite nilpotent group, Sylow subgroups commute and the group is their internal direct product; that finite decomposition is the route from local root data to a global statement. The present theorem does not assert that converse for infinite groups, does not replace the finite hypotheses by an unproved extension, and does not claim a classification of all nonnilpotent groups. It supplies the actual infinite sharpness example required here.")),
                Paragraph(Text("The formal inputs are pinned Mathlib results on cyclic reduction and unique roots in free groups, conjugation of natural powers, subgroup centralizers, DihedralGroup 0, and nilpotent quotients, together with the repository's NilpotentRootAmalgamation theorem. The displayed theorem is a repository derivation from those mature library mechanisms; no priority claim is made."))),
            DescribeRole.Theorem)
        )));
}
