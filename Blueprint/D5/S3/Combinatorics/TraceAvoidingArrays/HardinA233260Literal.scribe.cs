using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233260LiteralDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.";
    private const string LeanPrefix = "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.";
    private const string OriginalName = "Number of 5Xn 0..5 arrays with no element x(i,j) adjacent to itself or value 5-x(i,j) horizontally or antidiagonally, top left element zero, and 1 appearing before 2 3 and 4, and 2 appearing before 3 in row major order (unlabeled 6-colorings with no clashing color pairs).";
    private const string OriginalFormula = "Empirical: a(n) = 512*a(n-1) -65536*a(n-2) +2490368*a(n-3) +17825792*a(n-4) -2818572288*a(n-5) +51539607552*a(n-6) -274877906944*a(n-7) for n>11";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Automata/hardin2013a233260");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal five-row complementary-pair arrays with horizontal and antidiagonal bonds.",
        H("Five-row antidiagonal arrays"), Blocks(
            Paragraph(Text("An array is a function from Fin 5 times Fin n to Fin 6. "
                + "A bond joins (r,j) to (s,j+1) exactly when r=s or r.val=s.val+1. "
                + "It excludes equal colours and colours whose values sum to five. "
                + "The first entry is zero. The rank r.val*n+j.val defines the strict "
                + "row-major predecessor relation. No colour is required to occur.")),
            Node("Col", "Col", Eq(Own("Col"),Call("Prod",Fin(Num(3)),Call("Prod",Fin(Num(3)),Call("Prod",Fin(Num(3)),Call("Prod",Fin(Num(3)),Fin(Num(3))))))), false, false),
            Node("column", "column", All("c",Own("Col"),Eq(Typed(Own("column",V("c")),Arrow(Fin(Num(5)),Fin(Num(3)))),Vector(Call("Prod.fst" ,V("c")),Call("Prod.fst" ,Call("Prod.snd" ,V("c"))),Call("Prod.fst" ,Call("Prod.snd" ,Call("Prod.snd" ,V("c")))),Call("Prod.fst" ,Call("Prod.snd" ,Call("Prod.snd" ,Call("Prod.snd" ,V("c"))))),Call("Prod.snd" ,Call("Prod.snd" ,Call("Prod.snd" ,Call("Prod.snd" ,V("c")))))))), false, false),
            Node("compatible", "compatible", All("a",Own("Col"),All("b",Own("Col"),Eq(Own("compatible",V("a"),V("b")),Parenthesized(And(Ne(Own("column",V("a"),Num(0)),Own("column",V("b"),Num(0))),And(Ne(Own("column",V("a"),Num(1)),Own("column",V("b"),Num(1))),And(Ne(Own("column",V("a"),Num(2)),Own("column",V("b"),Num(2))),And(Ne(Own("column",V("a"),Num(3)),Own("column",V("b"),Num(3))),And(Ne(Own("column",V("a"),Num(4)),Own("column",V("b"),Num(4))),And(Ne(Own("column",V("a"),Num(1)),Own("column",V("b"),Num(0))),And(Ne(Own("column",V("a"),Num(2)),Own("column",V("b"),Num(1))),And(Ne(Own("column",V("a"),Num(3)),Own("column",V("b"),Num(2))),Ne(Own("column",V("a"),Num(4)),Own("column",V("b"),Num(3))))))))))))))), false, false),
            Node("cls", "cls", All("c",Own("Col"),Eq(Typed(Own("cls",V("c")),Fin(Num(41))),App(Vector(Num(0),Num(27),Num(27),Num(14),Num(9),Num(40),Num(14),Num(40),Num(9),Num(5),Num(18),Num(36),Num(23),Num(3),Num(31),Num(32),Num(22),Num(13),Num(5),Num(36),Num(18),Num(32),Num(13),Num(22),Num(23),Num(31),Num(3),Num(2),Num(24),Num(30),Num(17),Num(6),Num(37),Num(20),Num(34),Num(12),Num(8),Num(15),Num(39),Num(26),Num(1),Num(28),Num(38),Num(16),Num(10),Num(11),Num(33),Num(21),Num(35),Num(7),Num(19),Num(29),Num(25),Num(4),Num(2),Num(30),Num(24),Num(20),Num(12),Num(34),Num(17),Num(37),Num(6),Num(11),Num(21),Num(33),Num(29),Num(4),Num(25),Num(35),Num(19),Num(7),Num(8),Num(39),Num(15),Num(38),Num(10),Num(16),Num(26),Num(28),Num(1),Num(1),Num(26),Num(28),Num(15),Num(8),Num(39),Num(16),Num(38),Num(10),Num(6),Num(17),Num(37),Num(24),Num(2),Num(30),Num(34),Num(20),Num(12),Num(7),Num(35),Num(19),Num(33),Num(11),Num(21),Num(25),Num(29),Num(4),Num(3),Num(23),Num(31),Num(18),Num(5),Num(36),Num(22),Num(32),Num(13),Num(9),Num(14),Num(40),Num(27),Num(0),Num(27),Num(40),Num(14),Num(9),Num(13),Num(32),Num(22),Num(36),Num(5),Num(18),Num(31),Num(23),Num(3),Num(4),Num(29),Num(25),Num(21),Num(11),Num(33),Num(19),Num(35),Num(7),Num(12),Num(20),Num(34),Num(30),Num(2),Num(24),Num(37),Num(17),Num(6),Num(10),Num(38),Num(16),Num(39),Num(8),Num(15),Num(28),Num(26),Num(1),Num(1),Num(28),Num(26),Num(16),Num(10),Num(38),Num(15),Num(39),Num(8),Num(7),Num(19),Num(35),Num(25),Num(4),Num(29),Num(33),Num(21),Num(11),Num(6),Num(37),Num(17),Num(34),Num(12),Num(20),Num(24),Num(30),Num(2),Num(4),Num(25),Num(29),Num(19),Num(7),Num(35),Num(21),Num(33),Num(11),Num(10),Num(16),Num(38),Num(28),Num(1),Num(26),Num(39),Num(15),Num(8),Num(12),Num(34),Num(20),Num(37),Num(6),Num(17),Num(30),Num(24),Num(2),Num(3),Num(31),Num(23),Num(22),Num(13),Num(32),Num(18),Num(36),Num(5),Num(13),Num(22),Num(32),Num(31),Num(3),Num(23),Num(36),Num(18),Num(5),Num(9),Num(40),Num(14),Num(40),Num(9),Num(14),Num(27),Num(27),Num(0)),Typed(Call("Fin.mk",Add(Add(Add(Add(Val(Call("Prod.fst" ,V("c"))),Mul(Num(3),Val(Call("Prod.fst" ,Call("Prod.snd" ,V("c")))))),Mul(Num(9),Val(Call("Prod.fst" ,Call("Prod.snd" ,Call("Prod.snd" ,V("c"))))))),Mul(Num(27),Val(Call("Prod.fst" ,Call("Prod.snd" ,Call("Prod.snd" ,Call("Prod.snd" ,V("c")))))))),Mul(Num(81),Val(Call("Prod.snd" ,Call("Prod.snd" ,Call("Prod.snd" ,Call("Prod.snd" ,V("c"))))))))),Fin(Num(243)))))), false, false),
            Node("relabel", "relabel", All("e",Call("Equiv.Perm",Fin(Num(3))),Eq(Typed(Own("relabel",V("e")),Call("Equiv",Own("Col"),Own("Col"))),Call("Equiv.prodCongr",V("e"),Call("Equiv.prodCongr",V("e"),Call("Equiv.prodCongr",V("e"),Call("Equiv.prodCongr",V("e"),V("e"))))))), false, false),
            Node("class_relabel", "class_relabel", All("e",Call("Equiv.Perm",Fin(Num(3))),All("c",Own("Col"),Eq(Own("cls",Own("relabel",V("e"),V("c"))),Own("cls",V("c"))))), true, false),
            Node("Q", "Q", Eq(Typed(Own("Q"),Call("Matrix",Fin(Num(41)),Fin(Num(41)),Q("Int"))),Matrix(new Formula[]{Matrix(new Formula[]{Num(2),Num(2),Num(2),Num(2),Num(0),Num(2),Num(2),Num(0),Num(2)},new Formula[]{Num(1),Num(1),Num(0),Num(1),Num(1),Num(1),Num(0),Num(1),Num(0)},new Formula[]{Num(1),Num(1),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(1)},new Formula[]{Num(1),Num(1),Num(1),Num(1),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(1),Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(1),Num(1),Num(1),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(1),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(1),Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(1),Num(0),Num(0),Num(0),Num(1),Num(0),Num(1),Num(0)},new Formula[]{Num(1),Num(1),Num(1),Num(1),Num(0),Num(1),Num(1),Num(0),Num(1)},new Formula[]{Num(0),Num(0),Num(0),Num(1),Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(1)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(1),Num(1),Num(1),Num(0),Num(1),Num(1),Num(0),Num(1)},new Formula[]{Num(1),Num(1),Num(0),Num(0),Num(0),Num(1),Num(0),Num(1),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(1),Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(1),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(1),Num(1),Num(1),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(1),Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(1)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(1),Num(1),Num(1),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(1),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(1),Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(1),Num(0),Num(0),Num(0),Num(1),Num(0),Num(1),Num(0)},new Formula[]{Num(1),Num(1),Num(1),Num(1),Num(0),Num(1),Num(1),Num(0),Num(1)},new Formula[]{Num(0),Num(0),Num(0),Num(1),Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(1)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)}),Matrix(new Formula[]{Num(2),Num(0),Num(0),Num(0),Num(0),Num(2),Num(2),Num(0),Num(2)},new Formula[]{Num(1),Num(1),Num(0),Num(0),Num(0),Num(1),Num(0),Num(1),Num(0)},new Formula[]{Num(1),Num(0),Num(0),Num(0),Num(0),Num(1),Num(1),Num(0),Num(0)},new Formula[]{Num(1),Num(1),Num(0),Num(1),Num(1),Num(1),Num(0),Num(1),Num(0)},new Formula[]{Num(0),Num(0),Num(1),Num(0),Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(1),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(1),Num(0),Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(1),Num(0),Num(1),Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(1),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(1),Num(0),Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(1),Num(0),Num(1),Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(1),Num(0),Num(1),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(1),Num(1),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(1),Num(0),Num(1),Num(0)},new Formula[]{Num(1),Num(0),Num(0),Num(0),Num(0),Num(1),Num(1),Num(0),Num(1)},new Formula[]{Num(1),Num(1),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(1),Num(0),Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(1),Num(0),Num(1),Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)}),Matrix(new Formula[]{Num(2),Num(0),Num(0),Num(0),Num(0),Num(2),Num(2),Num(0),Num(2)},new Formula[]{Num(1),Num(1),Num(0),Num(0),Num(0),Num(1),Num(0),Num(1),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(1)},new Formula[]{Num(0),Num(0),Num(1),Num(0),Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(1),Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(1),Num(1),Num(0),Num(1)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(1),Num(0),Num(1),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(1)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(1),Num(0),Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(1),Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(1),Num(0),Num(1),Num(0)},new Formula[]{Num(1),Num(0),Num(0),Num(0),Num(0),Num(1),Num(1),Num(0),Num(1)},new Formula[]{Num(1),Num(1),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(1)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(1),Num(0),Num(1),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(1),Num(1),Num(0),Num(1)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(1)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)}),Matrix(new Formula[]{Num(2),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(1),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(1),Num(0),Num(1),Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(1),Num(0),Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(1),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(1)},new Formula[]{Num(1),Num(1),Num(0),Num(1),Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(1),Num(0),Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(1),Num(1),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(1),Num(0),Num(1),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(1),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(1),Num(0),Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(1),Num(0),Num(1),Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(1),Num(0),Num(1),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(1),Num(1),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(1),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(1),Num(0),Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(0),Num(1)},new Formula[]{Num(1),Num(1),Num(0),Num(1),Num(1),Num(0),Num(0),Num(0),Num(0)}),Matrix(new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(1),Num(0),Num(1),Num(1)},new Formula[]{Num(0),Num(0),Num(1),Num(0),Num(1)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(1),Num(1)},new Formula[]{Num(0),Num(0),Num(1),Num(0),Num(1)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(1),Num(0),Num(1)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(1),Num(1)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(0),Num(0),Num(1),Num(0),Num(1)},new Formula[]{Num(1),Num(0),Num(0),Num(0),Num(0)},new Formula[]{Num(1),Num(1),Num(0),Num(1),Num(1)})})), false, false),
            Node("classWeights", "classWeights", Eq(Typed(Own("classWeights"),Arrow(Fin(Num(41)),Q("Int"))),Vector(Num(3),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6),Num(6))), false, false),
            Node("W", "W", Eq(Typed(Own("W"),Arrow(Fin(Num(12)),Arrow(Fin(Num(41)),Q("Int")))),Matrix(new Formula[]{Matrix(new Formula[]{Num(1),Num(1),Num(1),Num(1),Num(1),Num(1),Num(1),Num(1),Num(1)},new Formula[]{Num(32),Num(16),Num(8),Num(16),Num(8),Num(8),Num(4),Num(4),Num(8)},new Formula[]{Num(324),Num(162),Num(108),Num(162),Num(54),Num(108),Num(72),Num(36),Num(90)},new Formula[]{Num(3744),Num(1692),Num(1152),Num(1656),Num(432),Num(1152),Num(726),Num(336),Num(924)},new Formula[]{Num(40404),Num(17832),Num(12648),Num(17382),Num(3864),Num(12648),Num(8094),Num(3324),Num(10218)},new Formula[]{Num(436584),Num(188052),Num(136128),Num(182976),Num(37776),Num(135978),Num(86472),Num(34188),Num(109848)},new Formula[]{Num(4677996),Num(1999236),Num(1461936),Num(1948170),Num(386868),Num(1455330),Num(926688),Num(356718),Num(1178040)},new Formula[]{Num(50046816),Num(21300108),Num(15641112),Num(20791860),Num(4076904),Num(15561330),Num(9902268),Num(3777432),Num(12589032)},new Formula[]{Num(534870876),Num(227362620),Num(167167956),Num(222058218),Num(43370256),Num(166285254),Num(105794832),Num(40244358),Num(134501088)},new Formula[]{Num(5714699808),Num(2428286892),Num(1786071108),Num(2372039916),Num(462744516),Num(1776553854),Num(1130218524),Num(429577152),Num(1436892528)},new Formula[]{Num(61051776924),Num(25939228116),Num(19081127928),Num(25339665234),Num(4941644988),Num(18979182138),Num(12074072952),Num(4588030326),Num(15350261016)},new Formula[]{Num(652216306656),Num(277099897740),Num(203843789832),Num(270698972820),Num(52785403032),Num(202753867506),Num(128986171596),Num(49009985160),Num(163985386296)}),Matrix(new Formula[]{Num(1),Num(1),Num(1),Num(1),Num(1),Num(1),Num(1),Num(1),Num(1)},new Formula[]{Num(16),Num(8),Num(4),Num(4),Num(8),Num(8),Num(4),Num(4),Num(2)},new Formula[]{Num(162),Num(72),Num(18),Num(36),Num(54),Num(108),Num(60),Num(48),Num(48)},new Formula[]{Num(1692),Num(624),Num(96),Num(336),Num(432),Num(1188),Num(630),Num(450),Num(486)},new Formula[]{Num(18012),Num(5934),Num(660),Num(3414),Num(3954),Num(12738),Num(6924),Num(4404),Num(5436)},new Formula[]{Num(193422),Num(60300),Num(5616),Num(36798),Num(39786),Num(137238),Num(74208),Num(45192),Num(58236)},new Formula[]{Num(2069382),Num(630552),Num(54876),Num(395094),Num(418638),Num(1469460),Num(794802),Num(474474),Num(624636)},new Formula[]{Num(22126926),Num(6683616),Num(571320),Num(4230582),Num(4449822),Num(15716778),Num(8489280),Num(5034972),Num(6677232)},new Formula[]{Num(236442918),Num(71231268),Num(6055104),Num(45225858),Num(47469054),Num(167959452),Num(90685686),Num(53679306),Num(71346924)},new Formula[]{Num(2526101382),Num(760417884),Num(64536228),Num(483242874),Num(506892534),Num(1794483762),Num(968763108),Num(573102660),Num(762233496)},new Formula[]{Num(26986703574),Num(8121775080),Num(688964268),Num(5162740950),Num(5414409822),Num(19170864012),Num(10349117706),Num(6121303698),Num(8142986700)},new Formula[]{Num(288297900318),Num(86758735104),Num(7358664744),Num(55153947462),Num(57839442558),Num(204802017882),Num(110558217504),Num(65389788876),Num(86991005040)}),Matrix(new Formula[]{Num(1),Num(1),Num(1),Num(1),Num(1),Num(1),Num(1),Num(1),Num(1)},new Formula[]{Num(4),Num(2),Num(2),Num(2),Num(4),Num(8),Num(4),Num(4),Num(8)},new Formula[]{Num(72),Num(24),Num(24),Num(12),Num(36),Num(90),Num(60),Num(30),Num(84)},new Formula[]{Num(756),Num(216),Num(252),Num(72),Num(324),Num(972),Num(654),Num(264),Num(906)},new Formula[]{Num(8244),Num(2088),Num(2616),Num(528),Num(3084),Num(10458),Num(7254),Num(2484),Num(9798)},new Formula[]{Num(88266),Num(21246),Num(28230),Num(4614),Num(31314),Num(111108),Num(77898),Num(24858),Num(104292)},new Formula[]{Num(943740),Num(220752),Num(303270),Num(45402),Num(330306),Num(1185714),Num(836082),Num(256680),Num(1113198)},new Formula[]{Num(10087338),Num(2335038),Num(3247422),Num(473514),Num(3513666),Num(12664848),Num(8941494),Num(2710746),Num(11875608)},new Formula[]{Num(107779896),Num(24868764),Num(34715958),Num(5021142),Num(37490946),Num(135292734),Num(95552982),Num(28855944),Num(126813030)},new Formula[]{Num(1151459670),Num(265428474),Num(370944006),Num(53524158),Num(400369098),Num(1445305332),Num(1020878634),Num(307940562),Num(1354550544)},new Formula[]{Num(12301097724),Num(2834784432),Num(3962993910),Num(571428762),Num(4276654674),Num(15439997250),Num(10906233570),Num(3288677688),Num(14469950022)},new Formula[]{Num(131411798202),Num(30281310222),Num(42336964590),Num(6103374090),Num(45685629426),Num(164943614496),Num(116510986758),Num(35129393658),Num(154579060152)}),Matrix(new Formula[]{Num(1),Num(1),Num(1),Num(1),Num(1),Num(1),Num(1),Num(1),Num(1)},new Formula[]{Num(16),Num(8),Num(4),Num(4),Num(8),Num(4),Num(2),Num(2),Num(2)},new Formula[]{Num(162),Num(78),Num(24),Num(48),Num(72),Num(18),Num(6),Num(12),Num(12)},new Formula[]{Num(1872),Num(786),Num(168),Num(498),Num(684),Num(108),Num(24),Num(84),Num(120)},new Formula[]{Num(20202),Num(8034),Num(1380),Num(5394),Num(6924),Num(870),Num(132),Num(798),Num(1236)},new Formula[]{Num(218292),Num(83760),Num(12918),Num(58230),Num(71868),Num(8472),Num(1002),Num(8568),Num(12942)},new Formula[]{Num(2338998),Num(886038),Num(130188),Num(625854),Num(762456),Num(88332),Num(9474),Num(91824),Num(135966)},new Formula[]{Num(25023408),Num(9424500),Num(1366158),Num(6699618),Num(8127012),Num(936156),Num(97806),Num(983160),Num(1442394)},new Formula[]{Num(267435438),Num(100549590),Num(14514312),Num(71614974),Num(86765484),Num(9978108),Num(1033962),Num(10509900),Num(15375594)},new Formula[]{Num(2857349904),Num(1073736348),Num(154803954),Num(765192474),Num(926734584),Num(106523436),Num(11012070),Num(112298868),Num(164148678)},new Formula[]{Num(30525888462),Num(11469278094),Num(1652967300),Num(8174894358),Num(9899667984),Num(1137755148),Num(117535506),Num(1199747040),Num(1753245894)},new Formula[]{Num(326108153328),Num(122520837588),Num(17656009374),Num(87332803074),Num(105755358324),Num(12153813132),Num(1255290654),Num(12816982872),Num(18728674938)}),Matrix(new Formula[]{Num(1),Num(1),Num(1),Num(1),Num(1)},new Formula[]{Num(4),Num(2),Num(4),Num(4),Num(8)},new Formula[]{Num(36),Num(24),Num(24),Num(30),Num(54)},new Formula[]{Num(396),Num(240),Num(174),Num(294),Num(504)},new Formula[]{Num(4404),Num(2658),Num(1530),Num(3294),Num(5274)},new Formula[]{Num(47712),Num(28236),Num(15108),Num(35640),Num(56184)},new Formula[]{Num(511590),Num(302052),Num(156078),Num(383238),Num(599922)},new Formula[]{Num(5473992),Num(3225036),Num(1648644),Num(4099752),Num(6410148)},new Formula[]{Num(58505358),Num(34447908),Num(17551962),Num(43815402),Num(68483466)},new Formula[]{Num(625094184),Num(367985028),Num(187315224),Num(468129420),Num(731617620)},new Formula[]{Num(6678084414),Num(3931086252),Num(2000471382),Num(5001143310),Num(7815839562)},new Formula[]{Num(71342069304),Num(41995166556),Num(21368946228),Num(53427168792),Num(83495882436)})})), false, false),
            Node("quotient_rows", "quotient_rows", All("b",Own("Col"),All("s",Fin(Num(41)),Eq(Sum("c",Own("Col"),If(And(Own("compatible",V("b"),V("c")),Eq(Own("cls",V("c")),V("s"))),Typed(Num(1),Q("Int")),Typed(Num(0),Q("Int")))),Own("Q",Own("cls",V("b")),V("s"))))), true, false),
            Node("initial_class_counts", "initial_class_counts", All("i",Fin(Num(41)),Eq(Sum("a",Own("Col"),If(Eq(Own("cls",V("a")),V("i")),Typed(Num(1),Q("Int")),Typed(Num(0),Q("Int")))),Own("classWeights",V("i")))), true, false),
            Node("normal", "Strict row-major normalization", NormalFormula(), false, true),
            Node("Legal", "Literal array predicate", LegalFormula(), false, true),
            Node("a", "Literal finite count", CountFormula(), false, true),
            Node("Proper", "Proper pair-label pattern", ProperFormula(), false, false),
            Node("L", "Labelled three-colour count", LabelCountFormula(), false, false),
            Describe.Lean(DescribeId.Create("alternating"),
                DeclarationHandle.Create(Prefix + "alternating"),
                H("Column-parity colouring"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For any width and two labels a and b, the array has "
                    + "label a at every even column and label b at every odd column."))),
                DescribeRole.Definition),
            Node("columns_constant", "Omitting a label forces constant columns",
                ColumnsConstantFormula(), true, false),
            Describe.Lean(DescribeId.Create("two-label-classification"),
                DeclarationHandle.Create(Prefix + "two_label_classification"),
                H("Two remaining labels alternate with column parity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every width n at least two and every proper "
                    + "Fin 5 by Fin n array P into Fin 3 omitting a label d, there are "
                    + "distinct labels a and b such that P(r,j) is a at even j and b "
                    + "at odd j. Properness uses exactly the horizontal and "
                    + "antidiagonal bonds defined here. The classification applies "
                    + "to any stronger edge predicate containing those bonds."))),
                DescribeRole.Theorem),
            Node("counting_bridge", "Exact complementary-pair count", BridgeFormula(), true, false),
            Paragraph(Text("The pair labels identify {0,5}, {1,4}, and {2,3}. "
                + "Canonical first occurrences fix the pair names and the first side "
                + "of each used pair. A pattern with k used pairs has 2^(5*n-k) lifts. "
                + "At width at least two, every proper pattern uses two or three labels, "
                + "and every orbit under label permutations has six members. When one "
                + "label is omitted, the common neighbours of consecutive rows force "
                + "each column to be constant, including the last column. The two "
                + "remaining labels alternate with column parity. Exactly one such "
                + "pattern is canonical. Summing the two possible lift weights gives "
                + "the displayed identity.")),
            Node("pair_base", "The first pair-label recurrence", PairFormula(false), true, false),
            Node("pair_tail", "The pair-label recurrence at every larger width", PairFormula(true), true, false),
            Node("result", "The seven-lag integer recurrence", RecurrenceFormula(), true, true),
            Paragraph(Text("Column states record five independent pair labels. Relabelling "
                + "reduces their transitions to forty-one classes. The transfer polynomial is "
                + "x^7-16*x^6+64*x^5-76*x^4-17*x^3+84*x^2-48*x+8. Its vector relation "
                + "holds after four transitions and its value at one is zero. The scalar "
                + "relation covers every index at least thirteen; the same finite power "
                + "table verifies index twelve. The counting bridge scales each lag "
                + "coefficient by a power of thirty-two. Every count used has positive "
                + "width. The final statement quantifies all integers greater than eleven.")))));
    private static DocumentBlock Node(string name, string title, Formula formula,
        bool theorem, bool literature) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature && !theorem ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(literature
                ? "OEIS A233260, revision 7, " + (name == "result" ? "FORMULA: " + OriginalFormula : "NAME: " + OriginalName)
                : title + "."))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("hardin233260"), ResolutionKind.Proved) : null);
    private static Formula ColumnsConstantFormula()
    {
        var n = V("n"); var p = V("P"); var d = V("d");
        var j = V("j"); var r = V("r"); var i = V("i");
        var cells = Product(Fin(D(5)), Fin(n));
        var omitted = All("i", cells, Ne(App(p, i), d));
        var constant = All("j", Fin(n), All("r", Fin(D(5)),
            Eq(App(p, Pair(r, j)), App(p, Pair(Typed(D(0), Fin(D(5))), j)))));
        var pattern = All("P", Arrow(cells, Fin(D(3))), Imp(Own("Proper", p),
            All("d", Fin(D(3)), Imp(omitted, constant))));
        return All("n", Q("Nat"), Imp(Le(D(2), n), pattern));
    }
    private static Formula BridgeFormula()
    {
        var n = V("n");
        return All("n", Q("Nat"), Imp(Le(D(2), n), Eq(
            Mul(D(4,8), Typed(Own("a", n), Q("Int"))),
            Mul(Power(Typed(D(3,2), Q("Int")), n),
                Add(Typed(Own("L", n), Q("Int")), D(6))))));
    }
    private static Formula ProperFormula()
    {
        var n=V("n"); var p=V("P"); var j=V("j"); var h=V("h"); var r=V("r"); var s=V("s");
        var cells=Product(Fin(D(5)),Fin(n));
        var adjacent=Or(Eq(r,s),Eq(Val(r),Add(Val(s),D(1))));
        var next=Typed(Call("Fin.mk",Add(Val(j),D(1)),h),Fin(n));
        var bonds=All("j",Fin(n),All("h",Lt(Add(Val(j),D(1)),n),
            All("r",Fin(D(5)),All("s",Fin(D(5)),Imp(adjacent,Ne(App(p,Pair(r,j)),App(p,Pair(s,next))))))));
        return All("n",Q("Nat"),All("P",Arrow(cells,Fin(D(3))),Eq(Own("Proper",p),Parenthesized(bonds))));
    }
    private static Formula LabelCountFormula()
    {
        var n=V("n"); var p=V("P"); var arrays=Arrow(Product(Fin(D(5)),Fin(n)),Fin(D(3)));
        return All("n",Q("Nat"),Eq(Own("L",n),Call("Finset.card",
            Call("Finset.filter",Fn("P",arrays,Own("Proper",p)),Q("Finset.univ")))));
    }
    private static Formula PairFormula(bool tail)
    {
        Formula B(int k) => Add(Typed(Own("L", tail ? Add(V("n"), Num(k)) : Num(k)), Q("Int")), D(6));
        int d = tail ? 1 : 0;
        var formula = Eq(B(12+d), Sub(Add(Sub(Add(Add(Sub(Mul(Num(16), B(11+d)),
            Mul(Num(64), B(10+d))), Mul(Num(76), B(9+d))), Mul(Num(17), B(8+d))),
            Mul(Num(84), B(7+d))), Mul(Num(48), B(6+d))), Mul(Num(8), B(5+d))));
        return tail ? All("n", Q("Nat"), formula) : formula;
    }
    private static Formula RecurrenceFormula()
    {
        var n=V("n");
        Formula A(int k) => Typed(Own("a",Call("Int.toNat",k==0 ? n : Sub(n,Num(k)))),Q("Int"));
        var rhs=Sub(Add(Sub(Add(Add(Sub(Mul(Num(512),A(1)),Mul(Num(65536),A(2))),
            Mul(Num(2490368),A(3))),Mul(Num(17825792),A(4))),Mul(Num(2818572288),A(5))),
            Mul(Num(51539607552),A(6))),Mul(Num(274877906944),A(7)));
        return All("n",Q("Int"),Imp(Lt(Num(11),n),Eq(A(0),rhs)));
    }

    private static Formula NormalFormula()
    {
        var n = V("n"); var a = V("A"); var p = V("p"); var q = V("q");
        var cells = Product(Fin(D(5)), Fin(n));
        Formula Rank(Formula x) => Add(Mul(Val(Call("Prod.fst", x)), n),
            Val(Call("Prod.snd", x)));
        Formula Earlier(byte colour) => Ex("q", cells,
            And(Lt(Rank(q), Rank(p)), Eq(App(a, q), Typed(D(colour), Fin(D(6))))));
        var current = App(a, p);
        var condition = All("p", cells, And(
            Imp(Or(Eq(current, Typed(D(2), Fin(D(6)))),
                Or(Eq(current, Typed(D(3), Fin(D(6)))),
                    Eq(current, Typed(D(4), Fin(D(6)))))), Earlier(1)),
            Imp(Eq(current, Typed(D(3), Fin(D(6)))), Earlier(2))));
        return All("n", Q("Nat"), All("A", Arrow(cells, Fin(D(6))),
            Eq(Own("normal", a), Parenthesized(condition))));
    }

    private static Formula LegalFormula()
    {
        var n = V("n"); var a = V("A"); var j = V("j");
        var r = V("r"); var s = V("s"); var h = V("h");
        var cells = Product(Fin(D(5)), Fin(n));
        var first = Ex("j", Fin(n),
            And(Eq(Val(j), D(0)), Eq(App(a, Pair(Typed(D(0), Fin(D(5))), j)),
                Typed(D(0), Fin(D(6))))));
        var adjacent = Or(Eq(r, s), Eq(Val(r), Add(Val(s), D(1))));
        var here = App(a, Pair(r, j));
        var next = App(a, Pair(s, Typed(Call("Fin.mk", Add(Val(j), D(1)), h), Fin(n))));
        var bonds = All("j", Fin(n), All("h", Lt(Add(Val(j), D(1)), n),
            All("r", Fin(D(5)), All("s", Fin(D(5)), Imp(adjacent,
                And(Ne(here, next), Ne(Add(Val(here), Val(next)), D(5))))))));
        return All("n", Q("Nat"), All("A", Arrow(cells, Fin(D(6))),
            Eq(Own("Legal", a), Parenthesized(And(first, And(bonds, Own("normal", a)))))));
    }

    private static Formula CountFormula()
    {
        var n = V("n"); var a = V("A");
        var arrays = Arrow(Product(Fin(D(5)), Fin(n)), Fin(D(6)));
        return All("n", Q("Nat"), Eq(Own("a", n), Call("Finset.card",
            Call("Finset.filter", Fn("A", arrays, Own("Legal", a)), Q("Finset.univ")))));
    }

    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Product(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { NamePart(part) } : new[] { Dot, NamePart(part) }).ToArray());
    private static Formula NamePart(string name)
    {
        var words = name.Split('_');
        Formula result = V(words[^1]);
        for (var i = words.Length - 2; i >= 0; --i)
            result = Seq(V(words[i]), Underscore, Grp(result));
        return Seq(Operatorname, Grp(result));
    }
    private static Formula Own(string name, params Formula[] args) =>
        Call(LeanPrefix + name, args);
    private static Formula Call(string name, params Formula[] args) => App(Q(name), args);
    private static Formula App(Formula f, params Formula[] args) =>
        new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula x, Formula type) =>
        Parenthesized(Seq(x, Colon, Sp, type));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Val(Formula x) => Call("Fin.val", x);
    private static Formula Fn(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, body));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula Vector(params Formula[] a)
    {
        if (a.Length <= 9) return Matrix(a);
        var groups = new List<Formula>();
        for (var i = 0; i < a.Length; i += 9)
        {
            var row = new List<Formula>();
            for (var j = i; j < a.Length && j < i + 9; j++) row.Add(a[j]);
            groups.Add(Matrix(row.ToArray()));
        }
        return Matrix(groups.ToArray());
    }
    private static Formula Sum(string n, Formula t, Formula b) => Seq(F.Sum,Underscore,Grp(V(n),Colon,Sp,t),Sp,Parenthesized(b));
    private static Formula If(Formula c, Formula y, Formula n) => Parenthesized(Seq(Q("if"),Sp,Parenthesized(c),Sp,Q("then"),Sp,y,Sp,Q("else"),Sp,n));
    private static Formula Matrix(params Formula[][] rows)
    {
        var a=new List<Formula>{Begin,Grp(F.Id("pmatrix"))};
        for(int i=0;i<rows.Length;i++) {if(i>0)a.Add(RowBreak);for(int j=0;j<rows[i].Length;j++){if(j>0)a.Add(Amp);a.Add(rows[i][j]);}}
        a.AddRange([End,Grp(F.Id("pmatrix"))]);return Seq(a.ToArray());
    }
}
