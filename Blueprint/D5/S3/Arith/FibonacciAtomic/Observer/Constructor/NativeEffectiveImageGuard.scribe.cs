using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativeEffectiveImageGuardDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create(
        "NativeEffectiveImageGuard",H("Finite Presburger construction for original canonical image filters"),Blocks(
            Describe.Lean(DescribeId.Create("native-effective-guarded-image-formula"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeEffectiveImageGuard.effective_image_guard"),
                H("Exact simultaneous acceptance for a guarded system"),GuardedStatement(),
                AssessedProvenance.FromRepo(),Blocks(
                    Paragraph(Text("The input I has one original finite tuple of natural parameters p. Each finite token index is an integer affine expression in that tuple, with its explicit nonnegativity guard. The original Presburger guard and every index guard are conjuncts of the constructed formula. The same derived rank map is used throughout the equations and all filter occurrences. Every original expression, offset, ground, ordered pair and repeated filter remains present.")),
                    Paragraph(Text("For a pair-guarded optional-definition system, a mode fixes each undefined state to one exceptional atom or assigns Omega. Its canonical extension is taken in the full native completion. The finite formula imageGuard is true exactly when the original parameter is legal and every original filter value on that same canonical extension belongs to its actual native image. The completion and the outputs have no finiteness or rationality restriction.")),
                    Paragraph(Text("Atomic terminal alternatives are supplied by atomicGuard, whose recursion decreases the requested target rank. A finite ground uses its finite native parse, retaining both atomic terminal alternatives and ordered pair closure. A finite parameter token T(q(p)+c) belongs to image t exactly when q(p)+c is at least t. Omega belongs to every image. For a decorated state rho(a)Y, a at least t makes the obligation true; otherwise it refers to the same state at threshold t-a.")),
                    Paragraph(Text("Set s to the maximum original filter threshold, including zero. There are finitely many state and threshold keys, with thresholds from zero through s. The pinned finite Cartesian-product list program enumerates all Boolean labelings of these keys. For each labeling the formula requires every selected state key to satisfy its finite positive defining clause, then requires all original filter expressions to pass under that same labeling. The disjunction over these finite labelings is a finite Presburger formula. This enumerates finite graph labels and does not enumerate parameter values or introduce independent ranks.")),
                    Paragraph(Text("For completeness, label each key by its actual image membership in the one canonical completed tuple. The exact native image decomposition satisfies every selected clause and every passing root expression. For soundness, a selected zero-decorated state unfolds its defining equation; a positive decorator either passes directly or reduces the threshold. Pair clauses retain both exact atomic exceptions and both child obligations. These obligations, together with already known image members, form a post-fixed relation for the completed image grammar. The existing native image corecursor supplies actual preimages for this relation. Thus arbitrary cycles are accepted precisely through greatest-fixed-point semantics, with no finite-prefix surrogate.")),
                    Paragraph(Text("All empty cases are included: an empty filter conjunction is true, a system may have no states or parameter atoms, and threshold zero is the whole completion. The construction asserts total finite syntax and exact semantics; it makes no polynomial bound or whole acquired-input synthesis claim."))
                ),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-effective-original-image-formula"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeEffectiveImageGuard.original_effective_image_guard"),
                H("Effective original-system acceptance with all reconstructed names"),OriginalStatement(),
                AssessedProvenance.FromRepo(),Blocks(
                    Paragraph(Text("An original system may contain arbitrary decorated root links. The program effectiveNormalForm inspects the original finite state list in order and selects the first syntactic root link. A self-link of weight zero becomes free; a positive self-link becomes Omega. A link to a different state is eliminated by the existing simultaneous substitution and inert-slot step. Both original expression maps are composed after every step. The strict decrease in the number of root links proves that the original number of states is sufficient fuel. Every step is the previously established exact two-way transformation of the entire completed solution relation.")),
                    Paragraph(Text("The normalized input keeps the original affine index list and original guard. Every filter occurrence is substituted through its original reconstruction, with its threshold and multiplicity retained. EffectiveMode chooses fixed or live alternatives exactly on the undefined states of this computed presentation. effectiveTotalMode adds inert entries at the defined names. EffectiveInMode reads that mode on the exact projected original valuation. The original canonical tuple effectiveCanonical reconstructs every original name from the one canonical normalized extension.")),
                    Paragraph(Text("The formula originalImageGuard first executes this finite syntactic normalization and then the finite guarded image construction. Its first equivalence states exact acceptance of every original filter on effectiveCanonical, together with the original Legal guard. Its second equivalence states existence of one entire original completed assignment satisfying all original equations, this same projected mode and all original filters, again at the same legal parameter tuple. The forward and reverse projection maps and finite-exception completeness establish the second equivalence.")),
                    Paragraph(Text("This gives the effective parameter acceptance assertion of Proposition 4.3 using a completely specified syntactic normalization. The canonical completed values themselves may be defined semantically by their unique guarded extension; the computed formula contains no semantic choice. All original completed values remain available to the existence quantifier, including non-rational ones. The result concerns functional systems and their retained image filters; the separate whole acquired-input synthesis and effective-prefix assertions require their own hypotheses and conclusions."))
                ),DescribeRole.Theorem)
        )));
    private static StatementSource GuardedStatement()
    {
        var n=V("n");var k=V("k");var m=V("m");var input=V("I");var mode=V("mode");var p=V("p");
        var canonical=Call("canonical",Call("equations",input),Call("ranks",input,p),V("guarded"),mode);
        var body=IffOf(Call("holds",Call("imageGuard",input,mode),Call("environment",p)),
            And(Call("Legal",input,p),Call("Passes",Call("ranks",input,p),canonical,Call("filters",input))));
        var statement=All("p",Arr(Call("Fin",n),V("Nat")),body);
        statement=All("mode",Call("Mode",Call("threshold",Call("filters",input)),m),statement);
        statement=All("guarded",Call("Guarded",Call("equations",input)),statement);
        statement=All("I",Call("Input",n,k,m),statement);
        statement=All("m",V("Nat"),statement);
        statement=All("k",V("Nat"),statement);
        statement=All("n",V("Nat"),statement);
        return StatementSource.FromAuthor(Disp(statement));
    }
    private static StatementSource OriginalStatement()
    {
        var n=V("n");var k=V("k");var m=V("m");var input=V("I");var mode=V("mode");var p=V("p");var v=V("v");
        var acceptance=Call("holds",Call("originalImageGuard",input,mode),Call("environment",p));
        var canonical=Call("effectiveCanonical",input,mode,p);
        var existence=Some("v",Arr(Call("Fin",m),V("CompletionTree")),
            And(Call("SourceSatisfies",input,p,v),And(Call("EffectiveInMode",input,mode,p,v),Call("SourcePasses",input,p,v))));
        var body=And(IffOf(acceptance,And(Call("Legal",input,p),Call("SourcePasses",input,p,canonical))),
            IffOf(acceptance,And(Call("Legal",input,p),existence)));
        var statement=All("p",Arr(Call("Fin",n),V("Nat")),body);
        statement=All("mode",Call("EffectiveMode",input),statement);
        statement=All("I",Call("Input",n,k,m),statement);
        statement=All("m",V("Nat"),statement);
        statement=All("k",V("Nat"),statement);
        statement=All("n",V("Nat"),statement);
        return StatementSource.FromAuthor(Disp(statement));
    }
    private static Formula V(string n)=>F.Id(n);
    private static Formula Par(Formula f)=>Seq(Open,f,Close);
    private static Formula Call(string n,params Formula[] args)=>new Formula.Apply(Seq(Operatorname,Grp(V(n))),[..args]);
    private static Formula And(Formula a,Formula b)=>Seq(Par(a),Sp,Land,Sp,Par(b));
    private static Formula IffOf(Formula a,Formula b)=>Seq(Par(a),Sp,Iff,Sp,Par(b));
    private static Formula Arr(Formula a,Formula b)=>Seq(a,Sp,To,Sp,b);
    private static Formula All(string n,Formula t,Formula b)=>Seq(Forall,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Some(string n,Formula t,Formula b)=>Seq(Exists,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
}
