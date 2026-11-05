using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Dice;

internal sealed class EaslickCycleSeedsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Dice/EaslickCycleSeeds.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/easlick2026minimaldice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit simple cycles provide small seeds for uniform nested padding.",
        H("Finite cycle seeds"),
        Blocks(
            Node("easlick-source-seed", "The six seed lists", "sourceSeed",
                "The function sourceSeed assigns the explicit sorted-die cycles at six, seven, eight, nine, ten and eleven faces; it is empty at all other natural arguments. The corresponding lengths are 6,14,29,10,110,14. The lists omit the repeated closure row. The seven- through ten-face lists are the source lists in Appendices G through J, and the eleven-face list is obtained from the seven-face list by shifting each seed label by two and adding two low and two high faces in alternating nested intervals.", DescribeRole.Definition),
            Node("easlick-check-steps", "Executable successive-edge scan", "checkSteps",
                "For arbitrary encoded vertices and a Boolean edge function, recursively scan each adjacent pair. Empty and singleton lists have no edge obligation. This executable operation takes no semantic chain law.", DescribeRole.Definition),
            Node("easlick-check-die", "Executable die validation", "checkDie",
                "At arbitrary face count n, check the exact list length, successive nondecreasing labels and the lower and upper label bounds. Repeated labels are allowed. Soundness derives global pairwise order using transitivity.", DescribeRole.Definition),
            Node("easlick-check-cycle", "Executable arbitrary cycle validation", "checkCycle",
                "For arbitrary n and any finite list of encoded dice, check nonemptiness, duplicate removal preserving length, die validation and exact win counts on the closed list. This scans the actual input and never assumes validity, distinctness or a graph law.", DescribeRole.Definition),
            Node("easlick-check-cycle-sound", "General cycle checker soundness", "checkCycle_sound",
                "For every n at least three and every encoded finite input c, successful checkCycle reconstructs HasCycle(n,length(c)) in the original graph defined by actual minimum unconditional win probabilities. Its only checking premise is the executable Boolean result; the true-minimum bridge supplies the interpretation of the tested edge counts.", DescribeRole.Theorem),
            Node("easlick-source-seed-check", "Actual first checker inputs", "sourceSeed_check",
                "The unchanged six source and derived seed lists, at n in 6,7,8,9,10,11, pass checkCycle by kernel reduction. This is a computed first-instance certificate for the general checker. It is consumed by checkCycle_sound in finite_cycle_witnesses and then by the complete conjecture proof; it is not an independent finite-case resolution.", DescribeRole.Theorem),
            Node("easlick-finite-cycle-witnesses", "The verified finite cycle lengths", "finite_cycle_witnesses",
                "There is a simple minimum-advantage cycle of length six for six-face dice, length fourteen for seven-face dice, length twenty-nine for eight-face dice, length ten for nine-face dice, length one hundred ten for ten-face dice, and length fourteen for eleven-face dice. Every die is sorted with valid labels, all vertices in each cycle are distinct, and every edge including the closing edge has the true minimum probability above one half. These assertions supply finite seeds and do not assert the unbounded parameter statement or the global upper bound at six.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), (declaration == "sourceSeed" ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(F.Disp(Statement(declaration)))), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
    private static Formula And(params Formula[] xs) => xs.Aggregate((a,b) => new Formula.Logic(a, FormulaLogicOperator.And,b));
    private static Formula.BoundVariable B(string name, Formula type) => new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) => new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.MemberOf,b);
    private static Formula Arrow(Formula a, Formula b) => F.Seq(F.Open,a,F.Sp,F.To,F.Sp,b,F.Close);
    private static Formula Len(Formula a) => Call("length",a);
    private static Formula At(Formula a, Formula i) => Call("at",a,i);
    private static Formula N => Id("Nat");
    private static Formula L => Call("List",N);
    private static Formula LL => Call("List",L);
    private static Formula T => Id("true");
    private static Formula Adjacent(Formula c, Func<Formula,Formula,Formula> relation) =>
        All(Imp(Lt(Add(Id("i"),Num(1)),Len(c)),relation(At(c,Id("i")),At(c,Add(Id("i"),Num(1))))),B("i",N));
    private static Formula Statement(string declaration)
    {
        Formula n=Id("n"),d=Id("d"),c=Id("c"),a=Id("A"),edge=Id("edge");
        return declaration switch
        {
            "checkSteps" => All(Iff(Equal(Call("checkSteps",edge,c),T),Adjacent(c,(x,y)=>Equal(new Formula.Apply(edge,[x,y]),T))),B("A",Id("Type")),B("edge",Arrow(a,Arrow(a,Id("Bool")))),B("c",Call("List",a))),
            "checkDie" => All(Iff(Equal(Call("checkDie",n,d),T),And(Equal(Len(d),n),Adjacent(d,Le),All(Imp(Mem(Id("x"),d),And(Le(Num(1),Id("x")),Le(Id("x"),n))),B("x",N)))),B("n",N),B("d",L)),
            "checkCycle" => All(Iff(Equal(Call("checkCycle",n,c),T),And(NotEqual(c,Call("nil")),Equal(Len(Call("dedup",c)),Len(c)),All(Imp(Mem(d,c),Equal(Call("checkDie",n,d),T)),B("d",L)),All(Imp(Lt(Id("i"),Len(c)),Equal(Call("winCount",At(c,Id("i")),At(c,new Formula.Modulo(Add(Id("i"),Num(1)),Len(c)))),Call("threshold",n))),B("i",N)))),B("n",N),B("c",LL)),
            "checkCycle_sound" => All(Imp(And(Le(Num(3),n),Equal(Call("checkCycle",n,c),T)),Call("HasCycle",n,Len(c))),B("n",N),B("c",LL)),
            "sourceSeed_check" => All(Imp(new Formula.Logic(Equal(n,Num(6)),FormulaLogicOperator.Or,new Formula.Logic(Equal(n,Num(7)),FormulaLogicOperator.Or,new Formula.Logic(Equal(n,Num(8)),FormulaLogicOperator.Or,new Formula.Logic(Equal(n,Num(9)),FormulaLogicOperator.Or,new Formula.Logic(Equal(n,Num(10)),FormulaLogicOperator.Or,Equal(n,Num(11))))))),Equal(Call("checkCycle",n,Call("sourceSeed",n)),T)),B("n",N)),
            "finite_cycle_witnesses" => And(Call("HasCycle",Num(6),Num(6)),Call("HasCycle",Num(7),Num(14)),Call("HasCycle",Num(8),Num(29)),Call("HasCycle",Num(9),Num(10)),Call("HasCycle",Num(10),Num(110)),Call("HasCycle",Num(11),Num(14))),
            _ => throw new ArgumentException("Unknown dice declaration",nameof(declaration))
        };
    }
}
