using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms;

internal sealed class PropagationLegsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/PrimeForms/PropagationLegs",
            "A crossing slot propagates three square-root-of-three legs and reduces its discriminant to a Pythagorean spectral line."),
        H("Propagation Identity"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("three-propagated-legs-and-spectral-line"),
                H("Three propagated legs and spectral line"),
                LeanTheorem("D5/S3/PrimeForms/PropagationLegs.propagation_identity"),
                Disp(Seq(
                    Forall, Sp, F.Id("A"), Comma, F.Id("u"), Comma, F.Id("D"), InMacro, Mathbb, Grp(F.Id("R")), Comma, Esc,
                    F.Id("A"), Neq, D(0), Sp, Land, Sp,
                    F.Id("D"), Eq, D(3), F.Id("A"), Caret, D(2), Plus, F.Id("u"), Caret, D(2), Sp,
                    Rightarrow, Sp,
                    Open,
                    F.Id("D"), Minus, D(3), F.Id("A"), Caret, D(2), Eq, F.Id("u"), Caret, D(2), Sp, Land, Sp,
                    F.Id("D"), Minus, D(3), Open, Frac, Grp(F.Id("u"), Minus, F.Id("A")), Grp(D(2)), Close, Caret, D(2),
                    Eq, Open, Frac, Grp(D(3), F.Id("A"), Plus, F.Id("u")), Grp(D(2)), Close, Caret, D(2), Sp, Land, Sp,
                    F.Id("D"), Minus, D(3), Open, Frac, Grp(F.Id("u"), Plus, F.Id("A")), Grp(D(2)), Close, Caret, D(2),
                    Eq, Open, Frac, Grp(D(3), F.Id("A"), Minus, F.Id("u")), Grp(D(2)), Close, Caret, D(2),
                    Close, Sp, Land, Sp,
                    Frac, Grp(Sqrt, Grp(F.Id("D"))), Grp(Vert, Sp, F.Id("A"), Sp, Vert), Eq,
                    Sqrt, Grp(D(3), Plus, Open, Frac, Grp(F.Id("u")), Grp(F.Id("A")), Close, Caret, D(2)), Dot)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The represented values A, (u-A)/2, and (u+A)/2 are all square-root-of-three "
                    + "legs of the same crossing slot. Their respective companions are u, "
                    + "(3A+u)/2, and (3A-u)/2. The same theorem records the spectral reduction "
                    + "of the normalized discriminant square root, with the nonzero-base "
                    + "hypothesis making the quotient well-defined.")))
            ))));
}
