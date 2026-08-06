using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase;

internal sealed class ZeroOrbitCongruenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Phase/ZeroOrbitCongruence",
                "Separate the finite congruence premise from the global norm exclusion in the 36-divisibility step."),
            H("Zero-Orbit Congruence"),
            Blocks(
                Paragraph(
                    Text("This module records the exact finite-ring part of a local-to-global divisibility argument. The local candidate disjunction modulo 36 remains an explicit premise; no residue enumeration is inferred from the two theorems below.")),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("eisenstein-norm-mod-three"),
                    H("Eisenstein norm residues modulo three"),
                    LeanTheorem(
                        "D5/S1/Phase/ZeroOrbitCongruence.eisenstein_norm_mod_three"),
                    In(Seq(Forall, Sp, F.Id("x"), Comma, F.Id("y"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Slash, D(3), Mathbb, Grp(F.Id("Z")), Comma, Esc, F.Id("x"), Caret, Grp(D(2)), Minus, F.Id("xy"), Plus, F.Id("y"), Caret, Grp(D(2)), Eq, D(0), Sp, Lor, Sp, F.Id("x"), Caret, Grp(D(2)), Minus, F.Id("xy"), Plus, F.Id("y"), Caret, Grp(D(2)), Eq, D(1))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The norm polynomial x^2 - xy + y^2 takes only residues zero and one in Z/3Z. The proof exhausts all nine residue pairs.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("thirty-six-local-to-global"),
                    H("The local candidates collapse to divisibility by 36"),
                    LeanTheorem(
                        "D5/S1/Phase/ZeroOrbitCongruence.thirty_six_dvd_of_local_candidates_and_eisenstein_norm"),
                    Disp(Seq(Forall, Sp, F.Id("m"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc, Forall, Sp, F.Id("x"), Comma, F.Id("y"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Slash, D(3), Mathbb, Grp(F.Id("Z")), Comma, Esc, Open, Open, F.Id("m"), Sp, Operatorname, Grp(F.Id("mod")), Sp, D(3, 6), Eq, D(0), Sp, Lor, Sp, F.Id("m"), Sp, Operatorname, Grp(F.Id("mod")), Sp, D(3, 6), Eq, D(8), Close, Sp, Land, Sp, Open, OpenBracket, F.Id("m"), CloseBracket, Underscore, Grp(D(3)), Eq, F.Id("x"), Caret, Grp(D(2)), Minus, F.Id("xy"), Plus, F.Id("y"), Caret, Grp(D(2)), Close, Close, Sp, Rightarrow, Sp, D(3, 6), Sp, Mid, Sp, F.Id("m"))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "If the local computation leaves residues zero and eight modulo 36, and the represented residue is an Eisenstein norm modulo three, the residue eight branch is impossible. The result does not prove the local 432-case computation that supplies the candidate disjunction.")))
                )),
[
                        DocumentEdge.TruthAnchor.Create(
                            LeanDeclarationRef.Create("D5/S1/Phase/ZeroOrbitCongruence.eisenstein_norm_mod_three")),
                        DocumentEdge.TruthAnchor.Create(
                            LeanDeclarationRef.Create("D5/S1/Phase/ZeroOrbitCongruence.thirty_six_dvd_of_local_candidates_and_eisenstein_norm")),
                    ]));
}
