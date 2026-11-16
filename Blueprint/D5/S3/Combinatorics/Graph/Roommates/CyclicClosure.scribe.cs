using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Roommates;

internal sealed class CyclicClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six-site cyclic closure for the exact Mertens range-two proof.",
        H("Cyclic closure"), Blocks(
            Paragraph(Text("A word w of length m has a signed assignment d and Certificate(w,d). The source cycle has m+6 labelled sites, hence supplier parameter n=m+1. Assignment(m) means Fin(m) to the integers. SuccessfulProfile(n) is the subtype of SourceModel.Profile(n) admitting an acceptable stable partial matching. The matching keeps every interior old pair and old single, fulfills each actual exterior request, and uses the existing six-site buffer involution for free sites. The profile retains all first m rankings and places every nonzero buffer partner first.")),
            Describe.Lean(DescribeId.Create("matching"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.matching"),
                H("Actual involutive source matching"), StatementSource.FromAuthor(MatchingFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sum of the old interval and the six buffer vertices is identified with the labelled source cycle. Interior reciprocity is supplied by the certificate; the existing request involution supplies all exterior and new pairs. Fixed points represent singles."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("profile"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.profile"),
                H("The extended profile"), StatementSource.FromAuthor(ProfileFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every old ranking is retained literally. A buffer ranking is the existing partnerFirst permutation for its actual signed assignment, including the fixed deterministic ranking at a single."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("acceptable"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.acceptable"),
                H("Acceptable pairs and singles"), StatementSource.FromAuthor(AcceptableFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each assignment is zero or one of the four literal signed source offsets. Thus every nonfixed pair is an actual acceptable edge of the source ring."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("stable"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.stable"),
                H("No cyclic blocking edge"), StatementSource.FromAuthor(StableFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Old--old edges use the exact rank transport and have no new wrap edge. A matched buffer endpoint ranks its partner first and rejects any proposed improvement. A buffer single is at position 3 or 4 in one-based numbering; all four cyclic neighbors are distinct matched buffer vertices. This also excludes an edge from an old single to a new single. The argument includes m=1 and its extra edge between buffer positions 1 and 6, m=2, and odd m. There is no parity or eventual-length hypothesis."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("close"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.close"),
                H("Map on successful profiles"), StatementSource.FromAuthor(CloseFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose one certificate per certified word, construct its profile and stable matching, and retain only the successful profile. Certificates and matching witnesses are not counted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("close-injective"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.close_injective"),
                H("Recover the old ranking word"), StatementSource.FromAuthor(InjectiveFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Equality of output profiles gives equality at each first-m coordinate, recovering the input word independently of which certificate was chosen."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("count-le-successful-profile-count"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.count_le_successful_profile_count"),
                H("The lower cyclic count comparison"), StatementSource.FromAuthor(CountFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write b(m) for the number of certified ranking words, and a(n) for the number of successful labelled source profiles with supplier parameter n and n+5 sites. The injection proves b(m) <= a(m+1), equivalently b(m) <= a_(m+6) when the subscript records sites. GrowthTransfer.result consumes this bridge for the exact d=1,r=2 probability theorem. General Conjecture 3 remains outside this scope."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cyclicbridge-wrap-val"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.wrap_val"),
                H("wrap_val"), StatementSource.FromAuthor(CyclicBridgeArithmeticFormula(0)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cyclic closure uses this coordinate or rank identity with the literal supplier offsets."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cyclicbridge-wrap-index"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.wrap_index"),
                H("wrap_index"), StatementSource.FromAuthor(CyclicBridgeArithmeticFormula(1)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cyclic closure uses this coordinate or rank identity with the literal supplier offsets."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cyclicbridge-wrap-add"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.wrap_add"),
                H("wrap_add"), StatementSource.FromAuthor(CyclicBridgeArithmeticFormula(2)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cyclic closure uses this coordinate or rank identity with the literal supplier offsets."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cyclicbridge-wrap-signed"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.wrap_signed"),
                H("wrap_signed"), StatementSource.FromAuthor(CyclicBridgeArithmeticFormula(3)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cyclic closure uses this coordinate or rank identity with the literal supplier offsets."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cyclicbridge-signed-bounds"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.signed_bounds"),
                H("signed_bounds"), StatementSource.FromAuthor(CyclicBridgeArithmeticFormula(4)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cyclic closure uses this coordinate or rank identity with the literal supplier offsets."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cyclicbridge-rank-wrap"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.rank_wrap"),
                H("rank_wrap"), StatementSource.FromAuthor(CyclicBridgeArithmeticFormula(5)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cyclic closure uses this coordinate or rank identity with the literal supplier offsets."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cyclicbridge-closing-old-nonblocking"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.closing_old_nonblocking"),
                H("closing_old_nonblocking"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every old--old edge in the literal source cycle has the original certificate nonblocking test, with actual signed-offset ranks for exterior partners and rank four for singles. The complete new and mixed edge argument and closure injection are supplied by CyclicClosure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cyclicbridge-closing-request-source-target"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.closing_request_source_target"),
                H("closing_request_source_target"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual buffer target of every closing request is the original signed-offset neighbor in the literal source cycle of size m+6. Both left and right exterior requests preserve their cyclic destinations."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cyclicbridge-closing-old-edge-local"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.closing_old_edge_local"),
                H("closing_old_edge_local"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A six-site closing buffer creates no wrap edge between old vertices. Every source edge with two old endpoints has integer separation at most two, including old lengths one and two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cyclicbridge-signed"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.signed"),
                H("signed"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The four supplier labels represent signed offsets 1,2,-1,-2 in that order."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cyclicbridge-wrap"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.wrap"),
                H("wrap"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Integer coordinates are reduced modulo N=n+5; all four neighbors remain distinct, including N=5."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cyclicbridge-displacement"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.displacement"),
                H("displacement"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A fixed point is a single with displacement zero. An acceptable matched vertex retains its unique signed source offset when the cycle is cut."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cyclicbridge-cut-certificate"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.cut_certificate"),
                H("cut_certificate"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Cut every acceptable stable partial matching to a certificate on the unchanged ranking word. Reciprocity holds for integer targets that remain inside. Target injectivity includes exterior targets, by reduction to the injective cyclic partner permutation. Internal stability uses exact rank correspondence and strict rank injectivity; singles retain rank four."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cyclicbridge-cut"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.cut"),
                H("cut"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The map preserves the ranking word exactly and changes only the existential proof. It counts profiles once, independently of the number of stable matching witnesses."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cyclicbridge-source-count-le-open-count"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.source_count_le_open_count"),
                H("source_count_le_open_count"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every n>=0, hence every cycle size N=n+5>=5, the number of successful source profiles is at most the number of certified words of length N. There is no parity restriction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cyclicbridge-source-probability-eq"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.source_probability_eq"),
                H("source_probability_eq"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each of N independent uniform neighbor rankings has 24 choices. The literal supplier probability is the number of successful profiles divided by 24^N."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cyclicbridge-source-probability-le-open-proportion"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.source_probability_le_open_proportion"),
                H("source_probability_le_open_proportion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cyclic cut gives the upper comparison p_N<=b_N/24^N. CyclicClosure supplies the inverse closure injection. PaddedCompletion supplies supermultiplicativity, and GrowthTransfer.result combines these bounds into the exact same-q theorem."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Telescope(Formula body) => All("m", Call("Nat"), All("w", Call("Word", F.Id("m")),
        All("d", Call("Assignment", F.Id("m")), All("h", Call("Certificate", F.Id("w"), F.Id("d")), body))));
    private static Formula MatchingFormula() => Disp(Telescope(Call("HasType", Call("matching", F.Id("h")), Call("Matching", Call("Fin", Add(F.Id("m"), D(6)))))));
    private static Formula ProfileFormula() => Disp(Telescope(Call("HasType", Call("profile", F.Id("h")), Call("Profile", Add(F.Id("m"), D(1))))));
    private static Formula AcceptableFormula() => Disp(Telescope(Call("IsAcceptable", Call("ring", Add(F.Id("m"),D(1))), Call("matching", F.Id("h")))));
    private static Formula StableFormula() => Disp(Telescope(Call("IsStable", Call("ring", Add(F.Id("m"),D(1))), Call("rank", Call("profile", F.Id("h"))), Call("matching", F.Id("h")))));
    private static Formula CloseFormula() => Disp(All("m",Call("Nat"), All("w",Call("CertifiedWord",F.Id("m")), Call("HasType",Call("close",F.Id("w")),Call("SuccessfulProfile",Add(F.Id("m"),D(1)))))));
    private static Formula InjectiveFormula() => Disp(All("m",Call("Nat"),Call("Injective",Call("close",F.Id("m")))));
    private static Formula CountFormula() => Disp(All("m",Call("Nat"),new Formula.Relation(Call("count",F.Id("m")),FormulaRelationOperator.LessThanOrEqual,Call("card",Call("SuccessfulProfile",Add(F.Id("m"),D(1)))))));

    private static Formula CyclicBridgeCall(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula CyclicBridgeAll(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula CyclicBridgeEq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula CyclicBridgeLe(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula CyclicBridgeAnd(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula CyclicBridgeAdd(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula CyclicBridgeArithmeticFormula(int which)
    {
        Formula n=F.Id("n"), i=F.Id("i"), a=F.Id("a"), b=F.Id("b"), z=F.Id("z"), s=F.Id("s"), p=F.Id("p");
        Formula nat=CyclicBridgeCall("Nat"), integer=CyclicBridgeCall("Int"), size=CyclicBridgeAdd(n,D(5)), vi=CyclicBridgeCall("intVal",i), ss=CyclicBridgeCall("signed",s);
        Formula body = which switch {
            0 => CyclicBridgeAll("n",nat,CyclicBridgeAll("z",integer,CyclicBridgeEq(CyclicBridgeCall("intVal",CyclicBridgeCall("wrap",n,z)),CyclicBridgeCall("mod",z,size)))),
            1 => CyclicBridgeAll("n",nat,CyclicBridgeAll("i",CyclicBridgeCall("Fin",size),CyclicBridgeEq(CyclicBridgeCall("wrap",n,vi),i))),
            2 => CyclicBridgeAll("n",nat,CyclicBridgeAll("a",integer,CyclicBridgeAll("b",integer,CyclicBridgeEq(CyclicBridgeCall("wrap",n,CyclicBridgeAdd(a,b)),CyclicBridgeAdd(CyclicBridgeCall("wrap",n,a),CyclicBridgeCall("wrap",n,b)))))),
            3 => CyclicBridgeAll("n",nat,CyclicBridgeAll("s",CyclicBridgeCall("Fin",D(4)),CyclicBridgeEq(CyclicBridgeCall("wrap",n,ss),CyclicBridgeCall("offset",n,s)))),
            4 => CyclicBridgeAll("s",CyclicBridgeCall("Fin",D(4)),CyclicBridgeAnd(CyclicBridgeLe(CyclicBridgeCall("neg",D(2)),ss),CyclicBridgeAnd(CyclicBridgeLe(ss,D(2)),new Formula.Relation(ss,FormulaRelationOperator.NotEqual,D(0))))),
            _ => CyclicBridgeAll("n",nat,CyclicBridgeAll("p",CyclicBridgeCall("Profile",n),CyclicBridgeAll("i",CyclicBridgeCall("Fin",size),CyclicBridgeAll("a",integer,
                new Formula.Logic(CyclicBridgeAnd(CyclicBridgeLe(CyclicBridgeCall("neg",D(2)),a),CyclicBridgeLe(a,D(2))),FormulaLogicOperator.Implies,
                    CyclicBridgeEq(CyclicBridgeCall("rank",p,i,CyclicBridgeCall("wrap",n,CyclicBridgeAdd(vi,a))),CyclicBridgeCall("offsetRank",CyclicBridgeCall("apply",p,i),a)))))))
        };
        return Disp(body);
    }
}
