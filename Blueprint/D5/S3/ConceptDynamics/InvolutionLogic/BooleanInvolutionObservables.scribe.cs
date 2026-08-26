using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InvolutionLogic;

internal sealed class BooleanInvolutionObservablesDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InvolutionLogic/BooleanInvolutionObservables.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Boolean observables split into flip and invariant parity sectors under an involution.",
        H("Boolean Involution Observables"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("xor-of-two-flip-observables-is-invariant"),
                DeclarationHandle.Create(Prefix + "xor_invariant_of_flips"),
                H("Two flip observables have invariant XOR"),
                StatementSource.FromAuthor(TwoFlipsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Each flip hypothesis says that applying the transformation negates "
                            + "the corresponding proposition-valued observable.")),
                    Paragraph(Text(
                        "Negating both inputs leaves their exclusive-or unchanged. Thus the "
                            + "pointwise XOR belongs to the invariant sector.")),
                    Paragraph(Text(
                        "No fixed-point-free or inhabited-carrier assumption is needed for "
                            + "this parity identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("xor-of-flip-and-invariant-observables-flips"),
                DeclarationHandle.Create(Prefix + "xor_flip_of_flip_invariant"),
                H("A flip observable XOR an invariant observable still flips"),
                StatementSource.FromAuthor(FlipInvariantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The first observable changes truth value under the transformation, "
                            + "while the second retains its truth value.")),
                    Paragraph(Text(
                        "Pointwise exclusive-or therefore changes truth value exactly once, "
                            + "so the resulting observable satisfies PropFlip."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Bindings(
        Formula carrier,
        Formula involution,
        Formula first,
        Formula second) =>
        Seq(
            Forall, Sp, involution, Colon, Sp, Arrow(carrier, carrier), Comma, Sp,
            first, Comma, Sp, second, Colon, Sp,
            Arrow(carrier, Seq(Operatorname, Grp(F.Id("Prop")))), Comma, Sp);

    private static Formula TwoFlipsFormula()
    {
        Formula carrier = F.Id("X");
        Formula involution = F.Id("iota");
        Formula first = F.Id("p");
        Formula second = F.Id("q");
        Formula hypotheses = Seq(
            Call("PropFlip", involution, first), Sp, Land, Sp,
            Call("PropFlip", involution, second));

        return Disp(Seq(
            Bindings(carrier, involution, first, second),
            Open, hypotheses, Close, Sp, Rightarrow, Sp,
            Call("PropInvariant", involution, Call("xorObservable", first, second)),
            Dot));
    }

    private static Formula FlipInvariantFormula()
    {
        Formula carrier = F.Id("X");
        Formula involution = F.Id("iota");
        Formula first = F.Id("p");
        Formula second = F.Id("q");
        Formula hypotheses = Seq(
            Call("PropFlip", involution, first), Sp, Land, Sp,
            Call("PropInvariant", involution, second));

        return Disp(Seq(
            Bindings(carrier, involution, first, second),
            Open, hypotheses, Close, Sp, Rightarrow, Sp,
            Call("PropFlip", involution, Call("xorObservable", first, second)),
            Dot));
    }
}
