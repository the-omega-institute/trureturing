using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Dice;

internal sealed class EaslickPaddedCyclesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Dice/EaslickPaddedCycles.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/easlick2026minimaldice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform padding supplies simple cycles beyond every face count above six.",
        H("EaslickPaddedCycles"),
        Blocks(
            Node("easlick-cycle-edge-at", "Every edge of a closed seed", "cycle_edge_at",
                "For every r,k and list c of length k, if c followed by its first entry is an Edge(r) chain and k is positive, then every position i below k has an edge to position (i+1) modulo k. The last position therefore returns to the first one."),
            Node("easlick-padded-cycle", "Uniform nested padding", "padded_cycle",
                "For every r at least three, every positive even k, and every t with r+6 at most r+2t, a simple k-cycle for r-face dice gives a simple k(t+1)-cycle for (r+2t)-face dice. Enumerate the clone blocks by j from zero through t and, inside each block, enumerate the seed positions. Adjacent positions have opposite parity, including block transitions and the final closing edge because k is even. The central faces recover the seed position, and the multiplicity of the first low label recovers j, proving that all k(t+1) vertices are distinct."),
            Node("easlick-longer-cycle", "All parameters above six", "longer_cycle",
                "For every natural n at least seven, some k greater than n satisfies HasCycle(n,k). The finite cycles cover seven through eleven. For even n at least twelve use the six-face six-cycle and t=(n-6)/2; for odd n at least thirteen use the seven-face fourteen-cycle and t=(n-7)/2. The resulting lengths are 6(t+1) and 14(t+1), respectively, and both strictly exceed n. All vertices are explicit valid dice in the same graph and every edge uses the actual attained unconditional minimum."),
            Node("easlick-not-s-above-six", "Failure of an exact n bound above six", "not_S_above_six",
                "For every natural n at least seven, S(n) is false: the simple longer cycle contradicts its universal upper-bound clause. No assumed existence premise is added to the target.")
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), (declaration == "sourceSeed" ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(StrataLint.Scribe.FormulaDsl.Disp(Statement(declaration)))), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose)), Paragraph(Text("Every position i in Fin(k) is read through its natural value when indexing a list or forming (i+1) modulo k. The notation head denotes head!, and the closed-chain expression includes the final edge. All lengths, clone indices, products, remainders and inequalities are over natural numbers."))), DescribeRole.Theorem);
    private static Formula.BoundVariable B(string name, Formula type) => new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) => new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Ex(Formula body, params Formula.BoundVariable[] variables) => new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula And(params Formula[] xs) => xs.Aggregate((a,b) => new Formula.Logic(a, FormulaLogicOperator.And,b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Not(Formula a) => new Formula.Not(a);
    private static Formula Len(Formula a) => Call("length",a);
    private static Formula N => Id("Nat");
    private static Formula L => Call("List",N);
    private static Formula LL => Call("List",L);
    private static Formula Closed(Formula n, Formula c) => Call("IsChain",Call("Edge",n),Call("append",c,Call("singleton",Call("head",c))));
    private static Formula Statement(string declaration)
    {
        Formula r=Id("r"),k=Id("k"),t=Id("t"),c=Id("c"),n=Id("n");
        Formula target=Add(r,Multiply(Num(2),t));
        return declaration switch
        {
            "cycle_edge_at" => All(Imp(And(Equal(Len(c),k),Closed(r,c),Lt(Num(0),k)),All(Call("Edge",r,Call("at",c,Id("i")),Call("at",c,new Formula.Modulo(Add(Id("i"),Num(1)),k))),B("i",Call("Fin",k)))),B("r",N),B("k",N),B("c",LL)),
            "padded_cycle" => All(Imp(And(Le(Num(3),r),Lt(Num(0),k),Equal(new Formula.Modulo(k,Num(2)),Num(0)),Le(Add(r,Num(6)),target),Call("HasCycle",r,k)),Call("HasCycle",target,Multiply(k,Add(t,Num(1))))),B("r",N),B("k",N),B("t",N)),
            "longer_cycle" => All(Imp(Le(Num(7),n),Ex(And(Lt(n,k),Call("HasCycle",n,k)),B("k",N))),B("n",N)),
            "not_S_above_six" => All(Imp(Le(Num(7),n),Not(Call("S",n))),B("n",N)),
            _ => throw new ArgumentException("Unknown dice declaration",nameof(declaration))
        };
    }

}
