using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase;

internal sealed class ZeroOrbitCongruenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create("Separate the finite congruence premise from the global norm exclusion in the 36-divisibility step.", H("Zero-Orbit Congruence"), Blocks(
                Paragraph(
                    Text("This module records the exact finite-ring part of a local-to-global divisibility argument. The local candidate disjunction modulo 36 remains an explicit premise; no residue enumeration is inferred from the two theorems below.")),
                Describe.Lean(DescribeId.Create("eisenstein-norm-mod-three"), DeclarationHandle.Create("D5/S1/Phase/ZeroOrbitCongruence.eisenstein_norm_mod_three"), H("Eisenstein norm residues modulo three"), StatementSource.FromAuthor(In(Seq(Forall, Sp, F.Id("x"), Comma, F.Id("y"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Slash, D(3), Mathbb, Grp(F.Id("Z")), Comma, Esc, F.Id("x"), Caret, Grp(D(2)), Minus, F.Id("xy"), Plus, F.Id("y"), Caret, Grp(D(2)), Eq, D(0), Sp, Lor, Sp, F.Id("x"), Caret, Grp(D(2)), Minus, F.Id("xy"), Plus, F.Id("y"), Caret, Grp(D(2)), Eq, D(1)))), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                        "The norm polynomial x^2 - xy + y^2 takes only residues zero and one in Z/3Z. The proof exhausts all nine residue pairs."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("thirty-six-local-to-global"), DeclarationHandle.Create("D5/S1/Phase/ZeroOrbitCongruence.thirty_six_dvd_of_local_candidates_and_eisenstein_norm"), H("The local candidates collapse to divisibility by 36"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("m"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc, Forall, Sp, F.Id("x"), Comma, F.Id("y"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Slash, D(3), Mathbb, Grp(F.Id("Z")), Comma, Esc, Open, Open, F.Id("m"), Sp, Operatorname, Grp(F.Id("mod")), Sp, D(3, 6), Eq, D(0), Sp, Lor, Sp, F.Id("m"), Sp, Operatorname, Grp(F.Id("mod")), Sp, D(3, 6), Eq, D(8), Close, Sp, Land, Sp, Open, OpenBracket, F.Id("m"), CloseBracket, Underscore, Grp(D(3)), Eq, F.Id("x"), Caret, Grp(D(2)), Minus, F.Id("xy"), Plus, F.Id("y"), Caret, Grp(D(2)), Close, Close, Sp, Rightarrow, Sp, D(3, 6), Sp, Mid, Sp, F.Id("m")))), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                        "If the local computation leaves residues zero and eight modulo 36, and the represented residue is an Eisenstein norm modulo three, the residue eight branch is impossible. The result does not prove the local 432-case computation that supplies the candidate disjunction."))), DescribeRole.Theorem))));
}
