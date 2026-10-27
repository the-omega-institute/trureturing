using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Sequenceability;
internal sealed class PositiveChargePortsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Sequenceability/PositiveChargePorts.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original-coordinate port cycles and avoiding words",
        H("Original-coordinate port cycles and avoiding words"), Blocks(
        Paragraph(Text("For an arbitrary original coordinate type X, originalSpan H is precisely the integer span of the coefficient-one Boolean rows of the original family H. Complete M Omega contains all nonempty proper Boolean supports whose rows belong to M; minimalFamily is its full inclusion-minimal family. neighborhood M Omega x records literal original-coordinate incidence. No saturation, quotient, field extension or cancellation of a scaled relation is used.")),
        Paragraph(Text("Geometry M Omega q records a family B of q-free minimal rows, each meeting at least two terminal rows through q. Every pair of distinct terminals has a common B-neighbour; every B row misses some terminal. Each original coordinate shared by b in B and terminal t has exactly the minimal-row neighbourhood {t,b}. Other original coordinates, including private, unused, parallel and exterior coordinates, are unrestricted. This structure is an explicit premise; it is not derived here from charge hypotheses.")),
        Paragraph(Text("Choose b0 in B and distinct terminal neighbours a,z, together with a terminal u not neighbouring b0. The rank is injective on terminals, with a least and z greatest. At b0 exactly the ports at z are red. At each other b exactly its least terminal neighbour has red ports. K supplies exterior blue coordinates, lies in Omega minus q, and is disjoint from each B row. The relation arc G Blue s t asks for a shared B row and an actual blue ORIGINAL coordinate at t. B witnesses can repeat.")),
        Describe.Lean(DescribeId.Create("port-cycle"),DeclarationHandle.Create(Prefix+"exists_portCycle"),
            H("Construct the reverse cycle using actual original blue ports"),StatementSource.FromAuthor(PortCycleStatement()),
            AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("The explicit paths a to u to z to a and the remaining terminal routes establish strong connectivity. Semicompleteness follows from pair coverage and the actual port colouring. Apply finite_semicomplete_hamilton to the reverse relation, then choose a blue original coordinate from each actual arc. PortStep e f records f.terminal to e.terminal through e.port. The closing step uses the same first port. Distinct terminal endpoints imply distinct blue coordinate IDs, even when B witnesses repeat."))),DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("native-word"),DeclarationHandle.Create(Prefix+"native_avoiding_word"),
            H("A literal word avoids every complete original Boolean row"),StatementSource.FromAuthor(WordStatement()),
            AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("The cycle C is an output, with no Hamilton-cycle or PortCycle premise. The exterior mixed-colouring premise concerns every q-free minimal row outside B. The disjoint decomposition premise concerns EVERY Complete row and expresses it as the union of an independent subfamily of the actual minimalFamily. Both remain explicit. The red coordinates alpha,beta and all local B-star colour witnesses are constructed."))),DescribeRole.Theorem),
        Paragraph(Text("For P equal to the original ports in reverse cyclic order, the literal cycleWord is (Omega minus insert q Blue minus {alpha,beta}).toList, followed by alpha,beta,q, then P, then (Blue minus P.toFinset).toList. Its permutation theorem preserves every original coordinate exactly once. It does not identify parallel coordinates or discard the exterior and private coordinates.")),
        Paragraph(Text("If a selected disjoint union contains q, exactly one selected terminal d contains q. For d=a, alpha is present and beta is forbidden by beta's exact neighbourhood {z,b0}. For any other terminal, its arrival port is present and the immediately preceding port is absent from the entire selected union. An interval joining q to that arrival port must cross the absent predecessor. If q is absent, any selected minimal row has both a red and a blue coordinate, so its interval crosses q. These arguments handle all complete rows, including larger disjoint unions. They reuse the original infix_avoid_separator proof in PrivatePairBooleanDescent.")),
        Paragraph(Text("This proves the stated conditional original-coordinate word construction. The derivation of Geometry from original positive charges, exterior obstruction exclusion and the separate universal-neighbour case are not supplied here. The whole positiveGood, fullGood and adaptive-merge conclusions remain open. The longest-cycle theorem is classical; the original-coordinate composition makes no literature-priority claim.")) )));

    private static Formula X => Id("X");
    private static Formula F => Call("Finset",X);
    private static Formula Omega => Id("Omega");
    private static Formula Q => Id("q");
    private static Formula G => Id("G");
    private static Formula B => Id("bzero");
    private static Formula A => Id("a");
    private static Formula Z => Id("z");
    private static Formula U => Id("u");
    private static Formula R => Id("rank");
    private static Formula K => Id("K");
    private static Formula M => Id("M");
    private static Formula T(Formula m) => Call("neighborhood",m,Omega,Q);
    private static Formula N(Formula m,Formula b) => Call("terminalNeighbors",m,Omega,Q,b);
    private static Formula Blue => Call("blue",G,B,Z,R,K);
    private static Formula Red => Call("red",G,B,Z,R,K);
    private static Formula GB => Call("B",G);
    private static Formula Rank(Formula t) => Call("apply",R,t);
    private static Formula CommonPremises(Formula m) => And(Member(B,GB),Member(A,N(m,B)),Member(Z,N(m,B)),NotEqual(A,Z),
        Member(U,T(m)),Not(Member(U,N(m,B))),
        AllIn("s",F,T(m),AllIn("t",F,T(m),To(Equal(Rank(Id("s")),Rank(Id("t"))),Equal(Id("s"),Id("t"))))),
        AllIn("t",F,T(m),Le(Rank(A),Rank(Id("t")))),AllIn("t",F,T(m),Le(Rank(Id("t")),Rank(Z))),
        AllIn("b",F,GB,Call("Disjoint",K,Id("b"))));
    private static Formula Telescope(Formula body, Formula m, bool word)
    {
        body=All("K",F,body);
        body=All("rank",Call("Function",F,Call("Nat")),body);
        foreach(var n in new[]{"u","z","a","bzero"}) body=All(n,F,body);
        body=All("G",Call("Geometry",m,Omega,Q),body);
        body=All("q",X,body); body=All("Omega",F,body);
        body=word ? All("H",Call("Finset",F),body) : All("M",Call("Submodule",new Formula.Integers(),Call("Function",X,new Formula.Integers())),body);
        return FormulaDsl.Disp(All("X",Call("Type"),WithEquality(X,body)));
    }
    private static Formula PortCycleStatement() => Telescope(To(CommonPremises(M),
        Call("Nonempty",Call("PortCycle",G,Blue,A))),M,false);
    private static Formula Decomposition(Formula m) => All("D",F,To(Call("Complete",m,Omega,Id("D")),
        Ex("E",Call("Finset",F),And(Subset(Id("E"),Call("minimalFamily",m,Omega)),
            Call("Independent",Id("E")),Equal(Id("D"),Call("biUnion",Id("E"),Call("id")))))));
    private static Formula WordStatement()
    {
        var m=Call("originalSpan",Id("H"));
        var family=Call("minimalFamily",m,Omega); var s=Id("S");
        var outside=AllIn("S",F,family,To(And(Not(Member(Q,s)),Not(Member(s,GB))),And(
            ExIn("x",X,s,Member(Id("x"),Red)),ExIn("y",X,s,Member(Id("y"),Blue)))));
        var c=Id("C"); var alpha=Id("alpha"); var beta=Id("beta");
        var p=Call("map",Call("snd"),Call("cons",Call("first",c),Call("tail",c)));
        var w=Call("cycleWord",Omega,Blue,Q,alpha,beta,p);
        var result=Ex("C",Call("PortCycle",G,Blue,A),Ex("alpha",X,Ex("beta",X,And(
            Member(alpha,A),Member(alpha,Red),Member(beta,Red),NotEqual(alpha,beta),
            Call("Perm",w,Call("toList",Omega)),All("t",Call("List",X),To(Call("IsInfix",Id("t"),w),
                Not(Call("Complete",m,Omega,Call("toFinset",Id("t"))))))))));
        var premises=And(Subset(K,Call("erase",Omega,Q)),CommonPremises(m),outside,Decomposition(m));
        return Telescope(To(premises,result),m,true);
    }
    private static Formula WithEquality(Formula v,Formula body) => FormulaDsl.Seq(FormulaDsl.OpenBracket,Call("DecidableEq",v),FormulaDsl.CloseBracket,FormulaDsl.Comma,FormulaDsl.Sp,body);
    private static Formula All(string n,Formula t,Formula b) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),t,b);
    private static Formula Ex(string n,Formula t,Formula b) => new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(n),t,b);
    private static Formula AllIn(string n,Formula t,Formula s,Formula b) => All(n,t,To(Member(Id(n),s),b));
    private static Formula ExIn(string n,Formula t,Formula s,Formula b) => Ex(n,t,And(Member(Id(n),s),b));
    private static Formula Member(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.MemberOf,b);
    private static Formula Subset(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.SubsetOf,b);
    private static Formula Le(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Not(Formula a) => new Formula.Not(a);
    private static Formula To(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula And(params Formula[] a) {var r=a[^1];for(var i=a.Length-2;i>=0;i--)r=new Formula.Logic(a[i],FormulaLogicOperator.And,r);return r;}
}
