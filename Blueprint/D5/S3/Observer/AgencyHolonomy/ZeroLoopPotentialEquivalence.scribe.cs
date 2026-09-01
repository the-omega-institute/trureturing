using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class ZeroLoopPotentialEquivalenceDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/AgencyHolonomy/ZeroLoopPotentialEquivalence."
            + "closed_path_zero_iff_exists_potential";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An additive cost on a connected path groupoid has zero closed-path sums exactly when it is the difference of a vertex potential.",
        H("Zero Loop Potential Equivalence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("closed-path-zero-iff-exists-potential"),
                DeclarationHandle.Create(Declaration),
                H("Zero closed-path costs are exactly potential differences"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The cost is additive under path composition and changes sign under "
                            + "inversion. A potential therefore telescopes around every closed "
                            + "path, giving zero total cost.")),
                    Paragraph(Text(
                        "Conversely, choose a base object and one path from it to every object. "
                            + "The cost of the chosen path defines the potential. Closing the "
                            + "comparison path with the inverse chosen path shows that every edge "
                            + "cost is the corresponding potential difference."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Hom(Formula source, Formula target) =>
        Call("Hom", source, target);

    private static Formula TheoremFormula()
    {
        Formula zType = F.Id("Z");
        Formula kType = F.Id("K");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula z = F.Id("z");
        Formula f = F.Id("f");
        Formula g = F.Id("g");
        Formula loop = F.Id("loop");
        Formula edge = F.Id("edge");
        Formula potential = F.Id("potential");
        Formula cost(Formula path) => Call("C", path);

        Formula compositionLaw = Seq(
            Forall, Sp, x, Comma, Sp, y, Comma, Sp, z, Colon, Sp, zType, Comma, Sp,
            f, Colon, Sp, Hom(x, y), Comma, Sp, g, Colon, Sp, Hom(y, z), Comma, Sp,
            cost(Call("compose", f, g)), Sp, Eq, Sp, cost(f), Sp, Plus, Sp, cost(g));
        Formula inverseLaw = Seq(
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, zType, Comma, Sp,
            f, Colon, Sp, Hom(x, y), Comma, Sp,
            cost(Call("inv", f)), Sp, Eq, Sp, Minus, Sp, cost(f));
        Formula zeroLoops = Seq(
            Forall, Sp, z, Colon, Sp, zType, Comma, Sp,
            loop, Colon, Sp, Hom(z, z), Comma, Sp,
            cost(loop), Sp, Eq, Sp, D(0));
        Formula potentialDifference = Seq(
            Exists, Sp, potential, Colon, Sp, new Formula.TypeArrow(zType, kType), Comma, Sp,
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, zType, Comma, Sp,
            edge, Colon, Sp, Hom(x, y), Comma, Sp,
            cost(edge), Sp, Eq, Sp, Call("potential", y), Sp, Minus, Sp,
            Call("potential", x));

        return Disp(Seq(
            Forall, Sp, zType, Colon, Sp, F.Id("Type"), Comma, Sp,
            kType, Colon, Sp, F.Id("Type"), Comma, Sp,
            F.Id("C"), Colon, Sp, Open,
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, zType, Comma, Sp,
            new Formula.TypeArrow(Hom(x, y), kType), Close, Comma, Sp,
            Call("Groupoid", zType), Sp, Land, Sp,
            Call("IsConnected", zType), Sp, Land, Sp,
            Call("AddCommGroup", kType), Sp, Land, Sp,
            Open, compositionLaw, Close, Sp, Land, Sp,
            Open, inverseLaw, Close, Sp, Rightarrow, Sp,
            Open, Open, zeroLoops, Close, Sp, Iff, Sp,
            Open, potentialDifference, Close, Close, Dot));
    }
}
