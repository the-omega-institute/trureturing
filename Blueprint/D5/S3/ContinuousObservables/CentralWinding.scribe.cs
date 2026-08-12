using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class CentralWindingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite cyclic winding update is a noncentral unitary whose cardinal power is the nonconstant central visible phase.",
        H("A Central Winding Phase over the Visible Circle"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-cyclic-winding-updates-have-a-nonidentity-central-cardinal-power"),
                DeclarationHandle.Create(
                    "D5/S3/ContinuousObservables/CentralWinding."
                    + "central_winding_certificate"),
                H("A finite cyclic winding update has a nonidentity central cardinal power"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("M"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    D(2), Sp, Leq, Sp, F.Id("M"), Sp, Rightarrow, Sp,
                    F.Id("U"), Underscore, Grp(F.Id("M")), Caret, Grp(F.Id("M")),
                    Sp, Eq, Sp, F.Id("Z"), Underscore, Grp(F.Id("M")), Sp, Land, Sp,
                    F.Id("U"), Underscore, Grp(F.Id("M")), Caret, Grp(F.Id("M")),
                    Sp, InMacro, Sp, Operatorname, Grp(F.Id("center")),
                    Open, F.Id("A"), Underscore, Grp(F.Id("M")), Close, Sp, Land, Sp,
                    F.Id("Z"), Underscore, Grp(F.Id("M")), Sp, InMacro, Sp,
                    Operatorname, Grp(F.Id("center")),
                    Open, F.Id("A"), Underscore, Grp(F.Id("M")), Close, Sp, Land, Sp,
                    F.Id("U"), Underscore, Grp(F.Id("M")), Sp, InMacro, Sp,
                    Operatorname, Grp(F.Id("unitary")),
                    Open, F.Id("A"), Underscore, Grp(F.Id("M")), Close, Sp, Land, Sp,
                    F.Id("Z"), Underscore, Grp(F.Id("M")), Sp, InMacro, Sp,
                    Operatorname, Grp(F.Id("unitary")),
                    Open, F.Id("A"), Underscore, Grp(F.Id("M")), Close, Sp, Land, Sp,
                    F.Id("Z"), Underscore, Grp(F.Id("M")), Sp, Neq, Sp, D(1), Sp, Land, Sp,
                    Neg, Sp, Open, F.Id("U"), Underscore, Grp(F.Id("M")), Sp, InMacro, Sp,
                    Operatorname, Grp(F.Id("center")),
                    Open, F.Id("A"), Underscore, Grp(F.Id("M")), Close, Close, Sp, Land, Sp,
                    F.Id("z"), Open, D(0), Close, Sp, Neq, Sp,
                    F.Id("z"), Open, Frac, Grp(D(1)), Grp(D(2)), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every M at least two, let A_M be the algebra of continuous complex "
                        + "matrix fields indexed by ZMod M over the visible phase circle. The field "
                        + "U_M cyclically shifts the indices and places the circle coordinate z on "
                        + "its unique wrap edge; Z_M is the scalar field z times the identity. One "
                        + "full circuit crosses that edge exactly once, proving U_M to the M-th "
                        + "power equals Z_M and hence is central.")),
                    Paragraph(Text(
                        "Pointwise circle norm one proves that U_M and Z_M are unitary. At the "
                        + "half-turn, Z_M is minus the identity, so the central phase is not the "
                        + "identity. At phase zero, U_M fails to commute with a constant diagonal "
                        + "matrix field, proving that the update itself is noncentral.")),
                    Paragraph(Text(
                        "The certificate also proves z(0) differs from z(1/2). Every constant, "
                        + "winding-free phase configuration takes equal values at those points, so "
                        + "this clause excludes all such configurations. The M = 2 instance is kept "
                        + "explicitly: U_2 is [[0,z],[1,0]] and its square is Z_2. Local library "
                        + "searches checked weighted cyclic shifts, monomial matrices, permutation "
                        + "matrices, AddCircle.toCircle, and Unitary.mem_iff."))),
                DescribeRole.Theorem))));
}
