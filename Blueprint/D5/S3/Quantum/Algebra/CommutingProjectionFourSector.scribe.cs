using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class CommutingProjectionFourSectorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Commuting orthogonal projections admit the common four-sector decompositions.",
        H("Common Four-Sector Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("commuting-projections-have-four-equivalent-decompositions"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/CommutingProjectionFourSector."
                    + "commuting_projection_four_sector_criterion"),
                H("Commuting projections have four equivalent decompositions"),
                StatementSource.FromAuthor(FourSectorCriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let P and Q be orthogonal projections on an arbitrary complete real or "
                            + "complex inner-product space. Define the four sector operators by "
                            + "S11 = PQ, S10 = P(I-Q), S01 = (I-P)Q, and "
                            + "S00 = (I-P)(I-Q).")),
                    Paragraph(Text(
                        "The theorem retains all four conditions of the named source statement. "
                            + "They are: commutation of P and Q; projection of every sector "
                            + "operator; orthogonality and internal direct-sum completeness of "
                            + "the four ranges; and existence of four pairwise orthogonal "
                            + "projection outcomes whose sum is the identity and whose two "
                            + "marginals are P and Q.")),
                    Paragraph(Text(
                        "The reverse direct-sum implication uses uniqueness of sector "
                            + "components to make distinct sector products vanish, which recovers "
                            + "PQ = QP without a finite-dimensional or closed-range assumption.")),
                    Paragraph(Text(
                        "Loogle returned IsStarProjection.mul as an exact result for products of "
                            + "commuting projections, and the proof applies it. Pinned Mathlib "
                            + "also supplied the orthogonal-family, star-projection range, and "
                            + "internal direct-sum declarations used in the proof. Repository and "
                            + "LeanSearch queries found no theorem packaging the complete "
                            + "four-condition criterion."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[i]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula Indexed(Formula value, Formula first, Formula second) =>
        Seq(value, Underscore, Grp(first, second));

    private static Formula FourSectorCriterionFormula()
    {
        Formula scalar = F.Id("k");
        Formula space = F.Id("H");
        Formula p = F.Id("P");
        Formula q = F.Id("Q");
        Formula identity = F.Id("I");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula c = F.Id("c");
        Formula d = F.Id("d");
        Formula s = F.Id("S");
        Formula r = F.Id("R");
        Formula zero = D(0);
        Formula one = D(1);
        Formula binary = OpenBrace;
        Formula binaryEnd = CloseBrace;
        Formula sab = Indexed(s, a, b);
        Formula rab = Indexed(r, a, b);
        Formula rcd = Indexed(r, c, d);
        Formula s00 = Indexed(s, zero, zero);
        Formula s01 = Indexed(s, zero, one);
        Formula s10 = Indexed(s, one, zero);
        Formula s11 = Indexed(s, one, one);
        Formula r01 = Indexed(r, zero, one);
        Formula r10 = Indexed(r, one, zero);
        Formula r11 = Indexed(r, one, one);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, scalar, Comma, Sp, space, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("RCLike")), Open, scalar, Close,
            CloseBracket, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("NormedAddCommGroup")), Open, space,
            Close, CloseBracket, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("InnerProductSpace")), Open, scalar,
            Comma, Sp, space, Close, CloseBracket, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("CompleteSpace")), Open, space, Close,
            CloseBracket, Comma, RowBreak,
            Forall, Sp, p, Comma, Sp, q, Colon, Sp,
            Operatorname, Grp(F.Id("ContinuousLinearEnd")), Open, scalar, Comma, Sp,
            space, Close, Comma, Esc,
            Call("Projection", p), Sp, Land, Sp, Call("Projection", q), Comma, RowBreak,
            s11, Eq, p, q, Comma, Quad, Sp,
            s10, Eq, p, Open, identity, Minus, q, Close, Comma, Quad, Sp,
            s01, Eq, Open, identity, Minus, p, Close, q, Comma, Quad, Sp,
            s00, Eq, Open, identity, Minus, p, Close, Open, identity, Minus, q, Close,
            Comma, RowBreak,
            Left, OpenBracket,
            p, q, Eq, q, p,
            Right, CloseBracket, Sp, Leftrightarrow, Sp,
            Left, OpenBracket,
            Forall, Sp, a, Comma, Sp, b, InMacro, Sp, binary, zero, Comma, one,
            binaryEnd, Comma, Esc, Call("Projection", sab),
            Right, CloseBracket, Sp, Leftrightarrow, RowBreak,
            Left, OpenBracket,
            Call("OrthogonalFamily", Call("Ran", sab)), Sp, Land, Sp,
            Call("InternalDirectSum", Call("Ran", sab)),
            Right, CloseBracket, Sp, Leftrightarrow, RowBreak,
            Left, OpenBracket,
            Exists, Sp, r, Comma, Esc,
            Open, Forall, Sp, a, Comma, Sp, b, InMacro, Sp, binary, zero, Comma, one,
            binaryEnd, Comma, Esc, Call("Projection", rab), Close, Sp, Land, RowBreak,
            Open, Forall, Sp, a, Comma, Sp, b, Comma, Sp, c, Comma, Sp, d,
            InMacro, Sp, binary, zero, Comma, one, binaryEnd, Comma, Esc,
            Open, Open, a, Comma, b, Close, Neq, Open, c, Comma, d, Close,
            Rightarrow, Sp, rab, rcd, Eq, zero, Close, Close, Sp, Land, RowBreak,
            Sum, Underscore, Grp(a, Comma, b, InMacro, binary, zero, Comma, one,
            binaryEnd), rab, Eq, identity, Sp, Land, RowBreak,
            p, Eq, r10, Plus, r11, Sp, Land, Sp,
            q, Eq, r01, Plus, r11,
            Right, CloseBracket, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
