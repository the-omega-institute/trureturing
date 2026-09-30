using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class CompleteMappingEvenProductDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S3/Factorization/CompleteMappingEvenProduct.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit complete mapping on ZMod 2 times ZMod (2m) for every positive m.",
        H("Complete Mappings on an Even Product"),
        Blocks(
            Paragraph(Text("Let H_m be the additive group ZMod 2 times ZMod (2m), with m "
                + "positive. A complete mapping is a function theta on H_m for which theta "
                + "and x mapped to x + theta(x) are both bijective. Its graph consequently "
                + "selects every row, column and sum symbol of the addition table once.")),
            Describe.Lean(
                DescribeId.Create("complete-mapping-even-product-theta"),
                DeclarationHandle.Create(Root + "theta"), H("The explicit map"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("theta", F.Id("m"), F.Id("epsilon"), F.Id("j")), Sp, Eq, Sp,
                    Open, F.Id("epsilon"), Sp, Plus, Sp,
                    Call("h", F.Id("m"), F.Id("k")),
                    Comma, Sp, F.Id("k"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here k = j + epsilon.val in ZMod (2m), and h_m(k) "
                    + "is zero in ZMod 2 when k.val < m and one otherwise. epsilon.val "
                    + "is the standard representative zero or one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("complete-mapping-even-product-theorem"),
                DeclarationHandle.Create(Root + "theta_complete"),
                H("Both projected maps are permutations"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("m"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")),
                    Comma, Sp, D(0), Sp, Lt, Sp, F.Id("m"), Sp, Implies, Sp,
                    Call("Bijective", Call("theta", F.Id("m"))), Sp, Land, Sp,
                    Call("Bijective", Seq(F.Id("x"), Sp, Mapsto, Sp, F.Id("x"),
                        Sp, Plus, Sp, Call("theta", F.Id("m"), F.Id("x"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The first map is injective by recovering k and then "
                    + "epsilon. For the sum map, reduction modulo two recovers epsilon; "
                    + "doubling determines k modulo m, while h_m(k) selects its lower or "
                    + "upper lift in ZMod (2m). Both finite self-maps are therefore "
                    + "bijective. This proves only this explicit family, not a classification "
                    + "of complete mappings on all finite groups."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
}
