using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class ProductMinkowskiCovolumeDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/Lattices/ProductMinkowskiCovolume.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite product fundamental domains yield the discriminant covolume in every finite power.",
        H("Product Minkowski Covolume"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("product-basis-fundamental-domain"),
                DeclarationHandle.Create(Gid + "fundamentalDomain_pi"),
                H("Dependent finite products of basis fundamental domains"),
                StatementSource.FromAuthor(Factorization()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite type I and families of types J(i) and E(i), assume each E(i) "
                    + "is a normed additive commutative group and a real normed space, and let "
                    + "b(i) be a J(i)-indexed real basis of E(i). No finiteness of J(i) is assumed. "
                    + "FD denotes ZSpan.fundamentalDomain. The sigma-indexed Pi basis has "
                    + "exactly the component coordinate inequalities."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("product-basis-fundamental-domain-volume"),
                DeclarationHandle.Create(Gid + "volume_fundamentalDomain_pi"),
                H("Product volume for sigma-finite component measures"),
                StatementSource.FromAuthor(ProductVolume()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume all the hypotheses of the factorization theorem. In addition, each "
                    + "E(i) has a MeasureSpace whose volume is sigma-finite. The volume on the "
                    + "dependent function space is the canonical product measure. The equality "
                    + "is in the extended nonnegative reals and requires no Haar or Borel hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("product-minkowski-discriminant-covolume"),
                DeclarationHandle.Create(Gid + "restrictedMinkowskiLattice_covolume"),
                H("Discriminant covolume of the finite-power Minkowski lattice"),
                StatementSource.FromAuthor(Covolume()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let K be a field with a NumberField instance and let r be any natural number, "
                    + "including zero. The lattice is the existing restrictedMinkowskiLattice K r, "
                    + "with canonical product volume on Fin(r) to mixedSpace(K). The symbol c(K) "
                    + "denotes NumberField.InfinitePlace.nrComplexPlaces K and disc(K) denotes "
                    + "NumberField.discr K cast to the reals. The formula follows by applying the "
                    + "new product factorization to Mathlib's one-copy discriminant formula."))),
                DescribeRole.Theorem))));

    private static Formula Factorization() => Disp(Seq(
        Call("finite", F.Id("I")), Comma, Sp,
        Call("realNormedSpaces", F.Id("E")), Comma, Sp,
        Call("bases", F.Id("b"), F.Id("J"), F.Id("E")), Sp, Rightarrow, Sp,
        Call("FD", Call("PiBasis", F.Id("b"))), Sp, Eq, Sp,
        Call("SetPi", F.Id("I"), Call("FD", Sub(F.Id("b"), F.Id("i"))))));

    private static Formula ProductVolume() => Disp(Seq(
        Call("finite", F.Id("I")), Comma, Sp,
        Call("realNormedSpaces", F.Id("E")), Comma, Sp,
        Call("bases", F.Id("b"), F.Id("J"), F.Id("E")), Comma, Sp,
        Call("sigmaFiniteVolumes", F.Id("E")), Sp, Rightarrow, Sp,
        Call("vol", Call("FD", Call("PiBasis", F.Id("b")))), Sp, Eq, Sp,
        Product(Call("vol", Call("FD", Sub(F.Id("b"), F.Id("i")))))));

    private static Formula Covolume() => Disp(Seq(
        Call("NumberField", F.Id("K")), Comma, Sp,
        F.Id("r"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Sp, Rightarrow, Sp,
        Call("covol", Call("restrictedMinkowskiLattice", F.Id("K"), F.Id("r"))),
        Sp, Eq, Sp, Pow(Grp(
            Pow(Grp(Pow(F.D(2), Seq(Minus, F.D(1)))), Call("c", F.Id("K"))), Sp,
            Times, Sp, Sqrt, Grp(Call("abs", Call("disc", F.Id("K"))))), F.Id("r"))));

    private static Formula Product(Formula body) => Seq(
        F.Prod, F.Underscore, Grp(F.Id("i"), InMacro, F.Id("I")), Sp, body);
    private static Formula Pow(Formula value, Formula exponent) => Seq(value, Caret, Grp(exponent));
    private static Formula Sub(Formula value, Formula index) => Seq(value, Underscore, Grp(index));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
