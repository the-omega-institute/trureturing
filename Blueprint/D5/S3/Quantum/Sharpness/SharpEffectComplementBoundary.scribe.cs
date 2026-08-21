using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Sharpness;

internal sealed class SharpEffectComplementBoundaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Projection complement is fixed-point-free, while effect complement fixes the half-identity.",
        H("Sharp and Effect Complement Fixed Points"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sharp-effect-complement-boundary"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Sharpness/SharpEffectComplementBoundary."
                    + "sharp_effect_complement_boundary"),
                H("Projection complement is sharp-fixed-point-free but fixes a general effect"),
                StatementSource.FromAuthor(BoundaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let H be a nonzero finite-dimensional complex Hilbert space and let its "
                        + "continuous endomorphisms carry the adjoint operation. For every sharp "
                        + "projection P, I-P is again a sharp projection and differs from P.")),
                    Paragraph(Text(
                        "Positivity is the library predicate requiring a symmetric, equivalently "
                        + "self-adjoint, operator with nonnegative quadratic form. Thus an effect E "
                        + "is stated directly by Pos(E) and Pos(I-E). Both conditions hold for "
                        + "I/2, and complement fixes I/2 exactly.")),
                    Paragraph(Text(
                        "It follows that any codomain twist declared fixed-point-free on every "
                        + "effect must differ from ordinary complement. The proof uses Mathlib's "
                        + "projection-complement closure theorem directly; projection non-fixedness "
                        + "then follows from idempotence and nontriviality of H."))),
                DescribeRole.Theorem))));

    private static Formula BoundaryFormula()
    {
        Formula space = F.Id("H");
        Formula endomorphism = Call("End", space);
        Formula identity = F.Id("I");
        Formula projection = F.Id("P");
        Formula effect = F.Id("E");
        Formula complementProjection = Seq(identity, Sp, Minus, Sp, projection);
        Formula complementEffect = Seq(identity, Sp, Minus, Sp, effect);
        Formula half = Seq(Frac, Grp(D(1)), Grp(D(2)), identity);
        Formula complementHalf = Seq(identity, Sp, Minus, Sp, half);
        Formula positiveHalf = Call("Pos", half);
        Formula positiveComplementHalf = Call("Pos", complementHalf);
        Formula effectPremise = Seq(
            Call("Pos", effect), Sp, Land, Sp, Call("Pos", complementEffect));

        return Disp(Seq(
            Forall, Sp, space, Comma, Sp,
            D(0), Sp, Lt, Sp, Operatorname, Grp(F.Id("dim")),
            Underscore, Grp(Mathbb, Grp(F.Id("C"))), Open, space, Close,
            Sp, Lt, Sp, Infty, Comma, RowBreak, Grp(),
            Open, Forall, Sp, projection, Colon, Sp, endomorphism, Comma, Sp,
            Call("Projection", projection), Sp, Rightarrow, Sp,
            OpenBracket,
            Call("Projection", complementProjection), Sp, Land, Sp,
            complementProjection, Sp, Neq, Sp, projection,
            CloseBracket, Close, Sp, Land, RowBreak, Grp(),
            OpenBracket,
            positiveHalf, Sp, Land, Sp, positiveComplementHalf, Sp, Land, Sp,
            complementHalf, Sp, Eq, Sp, half,
            CloseBracket, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, Tau, Colon, Sp,
            new Formula.TypeArrow(endomorphism, endomorphism), Comma, Sp,
            Open, Forall, Sp, effect, Comma, Sp,
            effectPremise, Sp, Rightarrow, Sp,
            Tau, Open, effect, Close, Sp, Neq, Sp, effect,
            Close, Sp, Rightarrow, Sp,
            Tau, Sp, Neq, Sp,
            Open, effect, Sp, Mapsto, Sp, complementEffect, Close,
            Close, Dot));
    }
}
