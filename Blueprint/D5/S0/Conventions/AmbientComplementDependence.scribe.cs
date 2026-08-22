using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Conventions;

internal sealed class AmbientComplementDependenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Subtraction complement is defined only relative to an explicit ambient total.",
        H("Ambient Complement Dependence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("absolute-complement-requires-an-ambient-total"),
                DeclarationHandle.Create(
                    "D5/S0/Conventions/AmbientComplementDependence."
                        + "absolute_complement_requires_ambient_total"),
                H("Absolute complement requires an ambient total"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let G be an additive commutative group and let c_u(e) = u - e. At every "
                            + "fixed argument e, two complement values agree exactly when their "
                            + "ambient totals agree.")),
                    Paragraph(Text(
                        "The same equivalence holds for the whole complement operations. The "
                            + "reverse direction applies the frozen complement-encoding theorem, "
                            + "which recovers the ambient total by evaluating the operation at "
                            + "zero.")),
                    Paragraph(Text(
                        "Thus the formal operation always carries an explicit total parameter; "
                            + "there is no additional untyped complement term in this statement."))),
                DescribeRole.Theorem))));

    private static Formula Complement(Formula total, Formula argument) =>
        Seq(F.Id("c"), Underscore, total, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula group = F.Id("G");
        Formula u = F.Id("u");
        Formula v = F.Id("v");
        Formula e = F.Id("e");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, group, Colon, Sp,
                Operatorname, Grp(F.Id("Type")), Caret, Grp(Star), Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("AddCommGroup")), Open, group, Close,
                CloseBracket, Comma, RowBreak, Grp(),
            u, Comma, Sp, v, Comma, Sp, e,
                InMacro, Sp, group, Comma, RowBreak, Grp(),
            Open, Complement(u, e), Sp, Eq, Sp, Complement(v, e), Sp, Iff, Sp,
                u, Sp, Eq, Sp, v, Close, Sp, Land, RowBreak, Grp(),
            Open, F.Id("c"), Underscore, u, Sp, Eq, Sp, F.Id("c"), Underscore, v,
                Sp, Iff, Sp, u, Sp, Eq, Sp, v, Close, Comma, RowBreak, Grp(),
            Complement(u, F.Id("x")), Sp, Colon, Eq, Sp, u, Sp, Minus, Sp,
                F.Id("x"), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
