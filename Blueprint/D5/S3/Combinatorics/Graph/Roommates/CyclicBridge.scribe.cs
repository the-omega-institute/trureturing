using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Roommates;

internal sealed class CyclicBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cyclic cut and rank transport for the exact Mertens range-two proof.",
        H("CyclicBridge"), Blocks(
            Paragraph(Text("Declarations without a displayed formula retain explicit statement-projection gaps. Their descriptions state the model and proof roles; they do not claim a rendered formula for an unsupported projection.")),
            Describe.Lean(DescribeId.Create("wrap-val"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.wrap_val"),
                H("wrap_val"), StatementSource.FromAuthor(ArithmeticFormula(0)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cyclic closure uses this coordinate or rank identity with the literal supplier offsets."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("wrap-index"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.wrap_index"),
                H("wrap_index"), StatementSource.FromAuthor(ArithmeticFormula(1)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cyclic closure uses this coordinate or rank identity with the literal supplier offsets."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("wrap-add"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.wrap_add"),
                H("wrap_add"), StatementSource.FromAuthor(ArithmeticFormula(2)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cyclic closure uses this coordinate or rank identity with the literal supplier offsets."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("wrap-signed"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.wrap_signed"),
                H("wrap_signed"), StatementSource.FromAuthor(ArithmeticFormula(3)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cyclic closure uses this coordinate or rank identity with the literal supplier offsets."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signed-bounds"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.signed_bounds"),
                H("signed_bounds"), StatementSource.FromAuthor(ArithmeticFormula(4)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cyclic closure uses this coordinate or rank identity with the literal supplier offsets."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rank-wrap"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.rank_wrap"),
                H("rank_wrap"), StatementSource.FromAuthor(ArithmeticFormula(5)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cyclic closure uses this coordinate or rank identity with the literal supplier offsets."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("closing-old-nonblocking"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.closing_old_nonblocking"),
                H("closing_old_nonblocking"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every old--old edge in the literal source cycle has the original certificate nonblocking test, with actual signed-offset ranks for exterior partners and rank four for singles. The complete new and mixed edge argument and closure injection are supplied by CyclicClosure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("closing-request-source-target"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.closing_request_source_target"),
                H("closing_request_source_target"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual buffer target of every closing request is the original signed-offset neighbor in the literal source cycle of size m+6. Both left and right exterior requests preserve their cyclic destinations."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("closing-old-edge-local"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.closing_old_edge_local"),
                H("closing_old_edge_local"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A six-site closing buffer creates no wrap edge between old vertices. Every source edge with two old endpoints has integer separation at most two, including old lengths one and two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signed"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.signed"),
                H("signed"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The four supplier labels represent signed offsets 1,2,-1,-2 in that order."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("wrap"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.wrap"),
                H("wrap"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Integer coordinates are reduced modulo N=n+5; all four neighbors remain distinct, including N=5."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("displacement"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.displacement"),
                H("displacement"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A fixed point is a single with displacement zero. An acceptable matched vertex retains its unique signed source offset when the cycle is cut."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cut-certificate"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.cut_certificate"),
                H("cut_certificate"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Cut every acceptable stable partial matching to a certificate on the unchanged ranking word. Reciprocity holds for integer targets that remain inside. Target injectivity includes exterior targets, by reduction to the injective cyclic partner permutation. Internal stability uses exact rank correspondence and strict rank injectivity; singles retain rank four."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cut"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.cut"),
                H("cut"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The map preserves the ranking word exactly and changes only the existential proof. It counts profiles once, independently of the number of stable matching witnesses."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("source-count-le-open-count"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.source_count_le_open_count"),
                H("source_count_le_open_count"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every n>=0, hence every cycle size N=n+5>=5, the number of successful source profiles is at most the number of certified words of length N. There is no parity restriction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("source-probability-eq"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.source_probability_eq"),
                H("source_probability_eq"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each of N independent uniform neighbor rankings has 24 choices. The literal supplier probability is the number of successful profiles divided by 24^N."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("source-probability-le-open-proportion"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicBridge.source_probability_le_open_proportion"),
                H("source_probability_le_open_proportion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cyclic cut gives the upper comparison p_N<=b_N/24^N. CyclicClosure supplies the inverse closure injection. PaddedCompletion supplies supermultiplicativity, and GrowthTransfer.result combines these bounds into the exact same-q theorem."))), DescribeRole.Theorem))));
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula ArithmeticFormula(int which)
    {
        Formula n=F.Id("n"), i=F.Id("i"), a=F.Id("a"), b=F.Id("b"), z=F.Id("z"), s=F.Id("s"), p=F.Id("p");
        Formula nat=Call("Nat"), integer=Call("Int"), size=Add(n,D(5)), vi=Call("intVal",i), ss=Call("signed",s);
        Formula body = which switch {
            0 => All("n",nat,All("z",integer,Eq(Call("intVal",Call("wrap",n,z)),Call("mod",z,size)))),
            1 => All("n",nat,All("i",Call("Fin",size),Eq(Call("wrap",n,vi),i))),
            2 => All("n",nat,All("a",integer,All("b",integer,Eq(Call("wrap",n,Add(a,b)),Add(Call("wrap",n,a),Call("wrap",n,b)))))),
            3 => All("n",nat,All("s",Call("Fin",D(4)),Eq(Call("wrap",n,ss),Call("offset",n,s)))),
            4 => All("s",Call("Fin",D(4)),And(Le(Call("neg",D(2)),ss),And(Le(ss,D(2)),new Formula.Relation(ss,FormulaRelationOperator.NotEqual,D(0))))),
            _ => All("n",nat,All("p",Call("Profile",n),All("i",Call("Fin",size),All("a",integer,
                new Formula.Logic(And(Le(Call("neg",D(2)),a),Le(a,D(2))),FormulaLogicOperator.Implies,
                    Eq(Call("rank",p,i,Call("wrap",n,Add(vi,a))),Call("offsetRank",Call("apply",p,i),a)))))))
        };
        return Disp(body);
    }
}
