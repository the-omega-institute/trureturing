using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class KBonacciIrreversibleAcquisitionDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Algorithms/KBonacciIrreversibleAcquisition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete actual-history first-zero acquisition classification and uniform cost.",
        H("KBonacciIrreversibleAcquisition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("kbonacci-whole-first-zero-acquisition"),
                DeclarationHandle.Create(Owner + "whole_first_zero_acquisition"),
                H("Complete original first-zero acquisition theorem"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("m"), Colon, Sp, Seq(Mathbb,
                    Grp(F.Id("N"))), Comma, Sp, F.Id("ell"), Colon, Sp, Seq(Operatorname, Grp(F.Id("Bool"))), Comma, Sp, F.Id("Y"),
                    Colon, Sp, Seq(Operatorname, Grp(F.Id("Type"))), Comma, Sp, F.Id("target"), Colon, Sp, Seq(Seq(OpenBrace,
                    F.Id("q"), Colon, Sp, Call("Option", Call("LiveRecord", F.Id("k"))), Sp, Bar, Sp, Call("SourceRecord", F.Id("k"),
                    F.Id("m"), F.Id("q")), CloseBrace), Sp, To, Sp, F.Id("Y")), Comma, Sp, Seq(Open, Seq(Seq(Open, Seq(Seq(Open,
                    Seq(D(2), Sp, Leq, Sp, F.Id("k")), Close), Sp, Land, Sp, Seq(Open, Seq(D(1), Sp, Leq, Sp, F.Id("m")), Close)),
                    Close), Sp, Implies, Sp, Seq(Open, Seq(Seq(Operatorname, Grp(F.Id("let"))), Sp, F.Id("f"), Sp, Eq, Sp, Call("actualSourceTarget",
                    F.Id("target")), Semi, Sp, Seq(Seq(Open, Seq(Forall, Sp, F.Id("q"), Colon, Sp, Call("Option", Call("LiveRecord",
                    F.Id("k"))), Comma, Sp, Seq(Open, Seq(Seq(Open, Call("SourceRecord", F.Id("k"), F.Id("m"), F.Id("q")), Close),
                    Sp, Iff, Sp, Seq(Open, Seq(Exists, Sp, F.Id("history"), Colon, Sp, Call("List", Call("AllowedBlock", F.Id("k"),
                    F.Id("m"), F.Id("ell"))), Comma, Sp, Seq(Open, Seq(Call("historyRecord", F.Id("history")), Sp, Eq, Sp, F.Id("q")),
                    Close)), Close)), Close)), Close), Sp, Land, Sp, Seq(Open, Seq(Seq(Open, Call("RecordAcquired", F.Id("k"),
                    F.Id("m"), F.Id("ell"), F.Id("f")), Close), Sp, Iff, Sp, Seq(Open, Seq(Seq(Open, Call("FirstZeroCriterion",
                    F.Id("k"), F.Id("m"), F.Id("f"), D(0), D(0), F.Id("k"), Seq(OpenBrace, F.Id("phi"), Sp, Bar, Sp, Call("divides",
                    Call("gcd", F.Id("m"), Seq(F.Id("k"), Plus, D(1))), Call("val", F.Id("phi"))), CloseBrace)), Close), Sp, Land,
                    Sp, Seq(Open, Call("FirstZeroCriterion", F.Id("k"), F.Id("m"), F.Id("f"), D(1), D(0), F.Id("k"), Seq(OpenBrace,
                    F.Id("phi"), Sp, Bar, Sp, Call("divides", Call("gcd", F.Id("m"), Seq(F.Id("k"), Plus, D(1))), Call("val",
                    F.Id("phi"))), CloseBrace)), Close)), Close)), Close), Sp, Land, Sp, Seq(Open, Seq(Seq(Open, Call("RecordAcquired",
                    F.Id("k"), F.Id("m"), F.Id("ell"), F.Id("f")), Close), Sp, Implies, Sp, Seq(Open, Seq(Exists, Sp, F.Id("controller"),
                    Colon, Sp, Seq(Call("Option", Call("ZMod", D(2))), Sp, To, Sp, Call("AcquisitionTree", F.Id("k"), F.Id("m"),
                    F.Id("ell"), F.Id("Y"), Call("prefixBudget", F.Id("k"), F.Id("m"), F.Id("k")))), Comma, Sp, Seq(Open, Seq(Seq(Open,
                    Seq(Forall, Sp, F.Id("q"), Colon, Sp, Call("Option", Call("LiveRecord", F.Id("k"))), Comma, Sp, Seq(Open,
                    Seq(Seq(Open, Call("SourceRecord", F.Id("k"), F.Id("m"), F.Id("q")), Close), Sp, Implies, Sp, Seq(Open, Seq(Call("result",
                    Call("controller", Call("endpointReading", F.Id("q"))), F.Id("q")), Sp, Eq, Sp, Call("f", F.Id("q"))), Close)),
                    Close)), Close), Sp, Land, Sp, Seq(Open, Seq(Call("result", Call("controller", Seq(Operatorname, Grp(F.Id("none")))),
                    Seq(Operatorname, Grp(F.Id("none")))), Sp, Eq, Sp, Call("f", Seq(Operatorname, Grp(F.Id("none"))))), Close),
                    Sp, Land, Sp, Seq(Open, Seq(Call("archive", Call("controller", Seq(Operatorname, Grp(F.Id("none")))), Seq(Operatorname,
                    Grp(F.Id("none")))), Sp, Eq, Sp, Seq(OpenBracket, CloseBracket)), Close), Sp, Land, Sp, Seq(Open, Seq(Forall,
                    Sp, F.Id("q"), Colon, Sp, Call("Option", Call("LiveRecord", F.Id("k"))), Comma, Sp, Seq(Open, Seq(Call("length",
                    Call("archive", Call("controller", Call("endpointReading", F.Id("q"))), F.Id("q"))), Sp, Leq, Sp, Call("prefixBudget",
                    F.Id("k"), F.Id("m"), F.Id("k"))), Close)), Close)), Close)), Close)), Close), Sp, Land, Sp, Seq(Open, Seq(Seq(Open,
                    Seq(D(2), Sp, Leq, Sp, F.Id("m")), Close), Sp, Implies, Sp, Seq(Open, Seq(Call("prefixBudget", F.Id("k"),
                    F.Id("m"), F.Id("k")), Sp, Eq, Sp, Seq(Seq(Seq(Open, Seq(F.Id("k"), Minus, D(1)), Close), Slash, F.Id("m")),
                    Plus, Seq(Seq(Open, Seq(F.Id("k"), Plus, D(1)), Close), Slash, Call("gcd", F.Id("m"), Seq(F.Id("k"), Plus,
                    D(1)))))), Close)), Close), Sp, Land, Sp, Seq(Open, Seq(Forall, Sp, F.Id("F"), Colon, Sp, Seq(Call("List",
                    Call("AllowedBlock", F.Id("k"), F.Id("m"), F.Id("ell"))), Sp, To, Sp, F.Id("Y")), Comma, Sp, Seq(Open, Seq(Seq(Open,
                    Call("HistoryAcquired", F.Id("ell"), F.Id("F")), Close), Sp, Iff, Sp, Seq(Open, Seq(Exists, Sp, F.Id("z"),
                    Colon, Sp, Seq(Call("Option", Call("LiveRecord", F.Id("k"))), Sp, To, Sp, F.Id("Y")), Comma, Sp, Seq(Open,
                    Seq(Seq(Open, Seq(Forall, Sp, F.Id("history"), Colon, Sp, Call("List", Call("AllowedBlock", F.Id("k"), F.Id("m"),
                    F.Id("ell"))), Comma, Sp, Seq(Open, Seq(Call("z", Call("historyRecord", F.Id("history"))), Sp, Eq, Sp, Call("F",
                    F.Id("history"))), Close)), Close), Sp, Land, Sp, Seq(Open, Call("RecordAcquired", F.Id("k"), F.Id("m"), F.Id("ell"),
                    F.Id("z")), Close)), Close)), Close)), Close)), Close), Sp, Land, Sp, Seq(Open, Seq(Forall, Sp, F.Id("t"),
                    Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("v"), Colon, Sp, Call("ZMod", D(2)), Comma, Sp, F.Id("b"),
                    Colon, Sp, Seq(Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, Call("ZMod", D(2))), Comma, Sp, Seq(Open, Seq(Seq(OpenBrace,
                    F.Id("pair"), Sp, Bar, Sp, Seq(Exists, Sp, F.Id("phi"), Colon, Sp, Call("ZMod", Seq(F.Id("k"), Plus, D(1))),
                    Comma, Sp, F.Id("s"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Open, Seq(Seq(Open, Call("SourceRecord",
                    F.Id("k"), F.Id("m"), Call("some", F.Id("v"), F.Id("phi"), F.Id("s"))), Close), Sp, Land, Sp, Seq(Open, Call("OnesArchive",
                    F.Id("k"), F.Id("m"), F.Id("t"), F.Id("v"), F.Id("phi"), F.Id("s"), F.Id("b")), Close), Sp, Land, Sp, Seq(Open,
                    Seq(F.Id("pair"), Sp, Eq, Sp, Call("pair", Call("some", F.Id("v"), F.Id("phi"), F.Id("s")), Call("allOneOrbit",
                    F.Id("k"), F.Id("m"), F.Id("t"), Call("some", F.Id("v"), F.Id("phi"), F.Id("s"))))), Close)), Close)), CloseBrace),
                    Sp, Eq, Sp, Call("prefixRecords", F.Id("k"), F.Id("m"), F.Id("t"), Seq(F.Id("k"), Minus, Seq(F.Id("t"), Sp,
                    Cdot, Sp, F.Id("m"))), F.Id("v"), Seq(F.Id("v"), Plus, Seq(Sum, Underscore, Grp(Seq(F.Id("i"), Sp, Lt, Sp,
                    F.Id("t"))), Sp, Call("b", F.Id("i")))), Seq(OpenBrace, F.Id("phi"), Sp, Bar, Sp, Seq(Seq(Open, Call("divides",
                    Call("gcd", F.Id("m"), Seq(F.Id("k"), Plus, D(1))), Call("val", F.Id("phi"))), Close), Sp, Land, Sp, Seq(Open,
                    Seq(Forall, Sp, F.Id("i"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Open, Seq(Seq(Open, Seq(F.Id("i"),
                    Sp, Lt, Sp, F.Id("t")), Close), Sp, Implies, Sp, Seq(Open, Seq(Call("allOneIncrement", F.Id("k"), F.Id("m"),
                    F.Id("i"), F.Id("phi")), Sp, Eq, Sp, Call("b", F.Id("i"))), Close)), Close)), Close)), CloseBrace))), Close)),
                    Close))), Close)), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every k>=2, m>=1, either full or internally legal block "
                        + "alphabet, arbitrary label type Y and initial record target "
                        + "f on the actual SourceRecord subtype Q, six conclusions hold. "
                        + "actualSourceTarget extends f outside Q using f(bottom). "
                        + "Only Q participates in acquisition. SourceRecord is exactly the image "
                        + "of one actual finite block history from the empty word, "
                        + "including bottom and every joint value-phase-tail record. "
                        + "Uniform RecordAcquired is equivalent to the two root "
                        + "FirstZeroCriterion conditions A_0(0,P) and A_1(0,P). "
                        + "Every acquired target has a controller of horizon "
                        + "D+1+L, where D=floor((k-1)/m) and L=phaseCost; its initial "
                        + "bottom branch stops with f(bottom), an empty archive and "
                        + "zero issued blocks. When m>=2 this horizon equals D+p. "
                        + "For every raw initial history target F, HistoryAcquired "
                        + "is equivalent to factorization through historyRecord by "
                        + "some uniformly acquired record target. Finally the actual "
                        + "successful all-one archive has exactly prefixRecords with "
                        + "h=k-t*m and the same-history phase filter I_i(theta)=b_i; "
                        + "the current value is v+sum b_i and the current tail is "
                        + "s+t*m, while the target still uses initial v,theta,s. "
                        + "The initial current reading freely selects a tree. Each "
                        + "later action uses only its attained complete-block endpoint. "
                        + "There is no resetting, source copying, internal-bit reading, "
                        + "target observability or decidable equality assumption. "
                        + "The statement is not an optimal-cost claim for L."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.Add(Comma);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
