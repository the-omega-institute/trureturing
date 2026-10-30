using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PrimitiveGaussSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Primitive Dirichlet Gauss sums are nonzero by finite Fourier injectivity.",
        H("Primitive Gauss sum nonvanishing"),
        Blocks(Describe.Lean(
            DescribeId.Create("primitive-gauss-sum-nonzero"),
            DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PrimitiveGaussSum.primitive_gaussSum_ne_zero"),
            H("Nonvanishing at every nonzero modulus"),
            StatementSource.FromAuthor(Disp(Seq(
                Forall, Sp, F.Id("N"), Colon, F.Id("Nat"), Comma, Sp,
                OpenBracket, Call("NeZero", F.Id("N")), CloseBracket, Sp,
                Forall, Sp, F.Id("chi"), Colon,
                Call("DirichletCharacter", F.Id("C"), F.Id("N")), Comma, Sp,
                Call("IsPrimitive", F.Id("chi")), Sp, Implies, Sp,
                Call("gaussSum", F.Id("chi"), Call("stdAddChar", F.Id("N"))),
                Sp, Neq, Sp, D(0)))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every natural modulus N with NeZero N and every primitive complex Dirichlet character chi modulo N, the standard additive-character Gauss sum is nonzero. The statement includes N=1 and composite moduli.")),
                Paragraph(Text("If the Gauss sum vanished, Mathlib's primitive Fourier-transform formula would force the discrete Fourier transform of chi to vanish. Injectivity of ZMod.dft would then make chi identically zero, contradicting its value one at one. This is a supporting API lemma using the classical finite Fourier theory already in Mathlib, with no claim of new mathematical novelty.")),
                Paragraph(Text("The intended consumer is nonzero normalization of the modular Dirichlet translation twist; its q-expansion coefficient law remains future work. The Reg candidate is kernel checked but sourceSelection is absent and declared_validated enrollment is not claimed. The remaining source-audit obligation is tracked at https://github.com/the-omega-institute/trureturing/issues/23614."))),
            DescribeRole.Theorem))));
}
