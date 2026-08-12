using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class LandauIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("The algebraic Landau identity for the finite-dimensional CHSH operator.",
        H("Landau Identity for Finite Matrix Observables"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-chsh-square-is-governed-by-local-commutators"),
                DeclarationHandle.Create("D5/S3/QuantumBounds/LandauIdentity.landau_identity"),
                H("The CHSH square is governed by local commutators"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("m"), Comma, Sp, F.Id("n"), Comma, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("m"), Close,
                    CloseBracket, Sp,
                    OpenBracket,
                    Operatorname, Grp(F.Id("DecidableEq")), Open, F.Id("m"), Close,
                    CloseBracket, Sp,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("n"), Close,
                    CloseBracket, Sp,
                    OpenBracket,
                    Operatorname, Grp(F.Id("DecidableEq")), Open, F.Id("n"), Close,
                    CloseBracket, Comma, Esc,
                    Forall, Sp,
                    F.Id("A"), Underscore, Grp(D(0)), Comma, Sp,
                    F.Id("A"), Underscore, Grp(D(1)), InMacro, Sp,
                    F.Id("M"), Underscore, Grp(F.Id("m")),
                    Open, Mathbb, Grp(F.Id("C")), Close, Comma, Esc,
                    Forall, Sp,
                    F.Id("B"), Underscore, Grp(D(0)), Comma, Sp,
                    F.Id("B"), Underscore, Grp(D(1)), InMacro, Sp,
                    F.Id("M"), Underscore, Grp(F.Id("n")),
                    Open, Mathbb, Grp(F.Id("C")), Close, Comma, Esc,
                    Open,
                    Operatorname, Grp(F.Id("Hermitian")), Open,
                    F.Id("A"), Underscore, Grp(D(0)), Close,
                    Sp, Land, Sp,
                    F.Id("A"), Underscore, Grp(D(0)), Caret, Grp(D(2)),
                    Eq, F.Id("I"), Underscore, Grp(F.Id("m")),
                    Close, Sp, Land, Sp,
                    Open,
                    Operatorname, Grp(F.Id("Hermitian")), Open,
                    F.Id("A"), Underscore, Grp(D(1)), Close,
                    Sp, Land, Sp,
                    F.Id("A"), Underscore, Grp(D(1)), Caret, Grp(D(2)),
                    Eq, F.Id("I"), Underscore, Grp(F.Id("m")),
                    Close, Sp, Land, Sp,
                    Open,
                    Operatorname, Grp(F.Id("Hermitian")), Open,
                    F.Id("B"), Underscore, Grp(D(0)), Close,
                    Sp, Land, Sp,
                    F.Id("B"), Underscore, Grp(D(0)), Caret, Grp(D(2)),
                    Eq, F.Id("I"), Underscore, Grp(F.Id("n")),
                    Close, Sp, Land, Sp,
                    Open,
                    Operatorname, Grp(F.Id("Hermitian")), Open,
                    F.Id("B"), Underscore, Grp(D(1)), Close,
                    Sp, Land, Sp,
                    F.Id("B"), Underscore, Grp(D(1)), Caret, Grp(D(2)),
                    Eq, F.Id("I"), Underscore, Grp(F.Id("n")),
                    Close, Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("let")), Sp,
                    F.Id("S"), Colon, Eq,
                    Operatorname, Grp(F.Id("kronecker")), Open,
                    F.Id("A"), Underscore, Grp(D(0)), Comma, Sp,
                    F.Id("B"), Underscore, Grp(D(0)), Close,
                    Plus,
                    Operatorname, Grp(F.Id("kronecker")), Open,
                    F.Id("A"), Underscore, Grp(D(0)), Comma, Sp,
                    F.Id("B"), Underscore, Grp(D(1)), Close,
                    Plus,
                    Operatorname, Grp(F.Id("kronecker")), Open,
                    F.Id("A"), Underscore, Grp(D(1)), Comma, Sp,
                    F.Id("B"), Underscore, Grp(D(0)), Close,
                    Minus,
                    Operatorname, Grp(F.Id("kronecker")), Open,
                    F.Id("A"), Underscore, Grp(D(1)), Comma, Sp,
                    F.Id("B"), Underscore, Grp(D(1)), Close,
                    Comma, Esc,
                    F.Id("C"), Colon, Eq, Minus,
                    Operatorname, Grp(F.Id("kronecker")), Open,
                    Open,
                    F.Id("A"), Underscore, Grp(D(0)), Sp,
                    F.Id("A"), Underscore, Grp(D(1)), Minus,
                    F.Id("A"), Underscore, Grp(D(1)), Sp,
                    F.Id("A"), Underscore, Grp(D(0)),
                    Close, Comma, Sp,
                    Open,
                    F.Id("B"), Underscore, Grp(D(0)), Sp,
                    F.Id("B"), Underscore, Grp(D(1)), Minus,
                    F.Id("B"), Underscore, Grp(D(1)), Sp,
                    F.Id("B"), Underscore, Grp(D(0)),
                    Close, Close,
                    Semi, Esc,
                    F.Id("S"), Caret, Grp(D(2)), Eq,
                    D(4), Cdot, Sp,
                    F.Id("I"), Underscore, Grp(F.Id("m"), Times, Sp, F.Id("n")),
                    Plus, F.Id("C")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let m and n be finite index types with decidable equality. Let A0 and A1 " +
                    "be Hermitian involutions in the m-by-m complex matrices, and let B0 and B1 " +
                    "be Hermitian involutions in the n-by-n complex matrices. For the displayed " +
                    "CHSH matrix S, its square is four times the identity plus C, where C is the " +
                    "negative Kronecker product of the two local commutators. The declaration " +
                    "proves this exact matrix equality. Hermiticity records the observable " +
                    "context, while the proof uses only the four involution equations. This is " +
                    "the algebraic kernel only: it introduces no state or variance, proves no " +
                    "positivity or norm estimate, and does not establish the three-gap " +
                    "decomposition, its saturation conditions, or the Tsirelson bound."))),
                DescribeRole.Theorem))));
}
