using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class EquivariantOverlapRecodingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/EquivariantOverlapRecoding.";
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula All(Formula body, params Formula.BoundVariable[] extra) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [B("U", F.Id("Type")), B("V", F.Id("Type")), B("I", F.Id("Type")),
             B("J", F.Id("Type")), B("H", F.Id("Type")), B("group", Call("Group", F.Id("H"))),
             B("d", Call("Boundary", F.Id("U"), F.Id("V"), F.Id("I"), F.Id("J"))),
             B("alpha", new Formula.TypeArrow(F.Id("U"), F.Id("H"))), .. extra], body);
    private static Formula L => Call("Prod", Call("LeftPath", F.Id("d")), F.Id("H"));
    private static Formula R => Call("Prod", Call("RightPath", F.Id("d")), F.Id("H"));
    private static Formula E(Formula p) => Call("encode", F.Id("d"), F.Id("alpha"), p);
    private static Formula D(Formula p) => Call("decode", F.Id("d"), F.Id("alpha"), p);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The boundary transfer supplies an equivariant conjugacy of the two skew-product dynamics.",
        H("Equivariant overlap recoding"), Blocks(
            Describe.Lean(DescribeId.Create("skew-overlap-input-recovery"),
                DeclarationHandle.Create(Prefix + "decode_encode"), H("Recover the input group coordinate"),
                StatementSource.FromAuthor(Disp(All(Equal(D(E(F.Id("p"))), F.Id("p")), B("p", L)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The first half-edge label multiplies the group coordinate on the right. The inverse code reads that half-edge in the preceding output and multiplies by its inverse."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("skew-overlap-output-recovery"),
                DeclarationHandle.Create(Prefix + "encode_decode"), H("Recover the output group coordinate"),
                StatementSource.FromAuthor(Disp(All(Equal(E(D(F.Id("p"))), F.Id("p")), B("p", R)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two group multipliers cancel in their written order, while the path inverse law recovers the full output history."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("skew-overlap-original-time"),
                DeclarationHandle.Create(Prefix + "encode_step"), H("Intertwine the original skew time step"),
                StatementSource.FromAuthor(Disp(All(Equal(
                    E(Call("leftStep", F.Id("d"), F.Id("alpha"), F.Id("beta"), F.Id("p"))),
                    Call("rightStep", F.Id("d"), F.Id("alpha"), F.Id("beta"), E(F.Id("p")))),
                    B("beta", new Formula.TypeArrow(F.Id("V"), F.Id("H"))), B("p", L)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The input product alpha(u_i) beta(v_i) and the transfer alpha(u_(i+1)) equal the transfer alpha(u_i) followed by the output product beta(v_i) alpha(u_(i+1)). Associativity suffices; the group need not commute."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("skew-overlap-preserves-left-action"),
                DeclarationHandle.Create(Prefix + "encode_equivariant"), H("Preserve the specified left group action"),
                StatementSource.FromAuthor(Disp(All(Equal(E(Call("translate", F.Id("g"), F.Id("p"))),
                    Call("translate", F.Id("g"), E(F.Id("p")))), B("g", F.Id("H")), B("p", L)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Left multiplication by a group element commutes with the constructed right boundary transfer. The same statement holds for the explicit inverse."))),
                DescribeRole.Theorem))));
}
