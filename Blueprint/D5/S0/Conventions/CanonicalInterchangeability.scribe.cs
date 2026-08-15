using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Conventions;

internal sealed class CanonicalInterchangeabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Faithful digit specifications are canonically interchangeable through decoding.",
        H("Canonical Interchangeability"),
        Blocks(
            Paragraph(
                Text("For any two faithful digit specifications whose word carriers decode equivalently to natural numbers, composing the decodings gives a bijection of digit words and a commuting decoding triangle.")),
            Describe.Lean(
                DescribeId.Create("faithful-digit-specifications-are-canonically-interchangeable"),
                DeclarationHandle.Create("D5/S0/Conventions/CanonicalInterchangeability.canonical_interchangeability"),
                H("Faithful digit specifications are canonically interchangeable"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Forall, Sp, F.Id("W"), Underscore, Grp(D(1)), Comma, Sp,
                    F.Id("W"), Underscore, Grp(D(2)), Comma, Sp,
                    F.Id("d"), Underscore, Grp(D(1)), Colon, Sp, F.Id("W"), Underscore, Grp(D(1)),
                    Equiv, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    F.Id("d"), Underscore, Grp(D(2)), Colon, Sp, F.Id("W"), Underscore, Grp(D(2)),
                    Equiv, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Operatorname, Grp(F.Id("Bijective")), Open,
                    F.Id("w"), Mapsto, Sp, F.Id("d"), Underscore, Grp(D(2)), Caret, Grp(Minus, D(1)),
                    Open, F.Id("d"), Underscore, Grp(D(1)), Open, F.Id("w"), Close, Close, Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("w"), Comma, Sp,
                    F.Id("d"), Underscore, Grp(D(2)), Open,
                    F.Id("d"), Underscore, Grp(D(2)), Caret, Grp(Minus, D(1)),
                    Open, F.Id("d"), Underscore, Grp(D(1)), Open, F.Id("w"), Close, Close, Close,
                    Eq, F.Id("d"), Underscore, Grp(D(1)), Open, F.Id("w"), Close, Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, Varphi, Comma, Sp, F.Id("w"), Comma, Sp,
                    Varphi, Open, F.Id("d"), Underscore, Grp(D(1)), Open, F.Id("w"), Close, Close,
                    Leftrightarrow, Varphi, Open,
                    F.Id("d"), Underscore, Grp(D(2)), Open,
                    F.Id("d"), Underscore, Grp(D(2)), Caret, Grp(Minus, D(1)),
                    Open, F.Id("d"), Underscore, Grp(D(1)), Open, F.Id("w"), Close, Close, Close,
                    Close, Close, Close, Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Bijective")), Open,
                    Operatorname, Grp(F.Id("wEncoding")), Caret, Grp(Minus, D(1)), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The first conjunct quantifies over every pair of faithful digit specifications whose word carriers decode equivalently to the natural numbers: composing one decoding with the inverse of the other is a bijection of digit words, that composite commutes with decoding, and any property factoring only through the decoded natural number holds of a word exactly when it holds of its transported image. The second conjunct exhibits the W-digit specification as a concrete inhabitant of the quantified domain, so the statement is not vacuous."))),
                DescribeRole.Theorem))));
}
