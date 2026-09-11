using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms;

internal sealed class PrimaryPseudoperfectPortCompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/PrimeForms/PrimaryPseudoperfectPortComposition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coprime products obey a quotient-derivative product rule whose residual ports compose exactly.",
        H("Primary Pseudoperfect Port Composition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("primary-pseudoperfect-port"),
                DeclarationHandle.Create(Prefix + "portDelta"),
                H("Port residual"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("Delta", R, C, B), Sp, Eq, Sp,
                    C, B, Sp, Minus, Sp, R, Call("d", B), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The port residual is natural subtraction of the charged quotient sum from the scaled factor."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("squarefree-derivative-coprime-product"),
                DeclarationHandle.Create(Prefix + "squarefreeDeriv_mul_of_coprime"),
                H("Coprime product rule for the quotient derivative"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("Coprime", A, B), Sp, Rightarrow, Sp,
                    Call("d", Seq(A, B)), Sp, Eq, Sp,
                    A, Call("d", B), Sp, Plus, Sp, B, Call("d", A), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Coprimality makes the prime-factor sets disjoint. Quotients indexed by a factor of A scale by B, while quotients indexed by a factor of B scale by A."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("port-coprime-composition"),
                DeclarationHandle.Create(Prefix + "portDelta_mul_of_coprime"),
                H("Ports compose across coprime factors"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("Coprime", A, B), Sp, Rightarrow, Sp,
                    Call("Delta", R, C, Seq(A, B)), Sp, Eq, Sp,
                    Call("Delta", Seq(R, A), Call("Delta", R, C, A), B), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The coprime product rule separates the two derivative charges. Distributivity over natural subtraction and successive subtraction then give the same result even when a residual reaches zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("primary-pseudoperfect-coprime-extension"),
                DeclarationHandle.Create(
                    Prefix + "isPPN_mul_squarefree_coprime_iff_portDelta_eq_one"),
                H("Coprime squarefree extension criterion"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("IsPPN", K), Sp, Land, Sp, Call("Squarefree", C), Sp, Land, Sp,
                    D(1), Sp, Lt, Sp, C, Sp, Land, Sp, Call("Coprime", K, C),
                    Sp, Rightarrow, Sp, Open,
                    Call("IsPPN", Seq(K, C)), Sp, Leftrightarrow, Sp,
                    C, Sp, Minus, Sp, K, Call("d", C), Sp, Eq, Sp, D(1), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Squarefreeness and nontriviality pass to the coprime product. Substituting the two quotient identities and cancelling the common term reduces primary pseudoperfectness to a unit port residual."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/PrimeForms/PrimaryPseudoperfectPorts"))]));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula A => F.Id("A");
    private static Formula B => F.Id("B");
    private static Formula C => F.Id("C");
    private static Formula K => F.Id("K");
    private static Formula R => F.Id("R");
}
