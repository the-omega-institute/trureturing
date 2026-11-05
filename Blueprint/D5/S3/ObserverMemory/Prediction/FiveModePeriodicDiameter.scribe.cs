using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class FiveModePeriodicDiameterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete law generated on a periodic B orbit cannot attain the diameter midpoint of two unequal-holding startup endpoints.",
        H("Five Mode Periodic Diameter Obstruction"), Blocks(
            Paragraph(Text("The source is FiniteStartFiveModeSource: p,q,r are positive and p+q+r<1, a=1-p-q and b=1-r. The visible alphabet is Fin 4 in the order 0,1,B,3, with B=2. First exits from source mode 2 lie in {1,3}; those from mode 4 lie in {0}. Write u=min(a,b), v=max(a,b). When a differs from b, 0<u<v<1. The dominant law is the pure source mode with holding v. The oriented mixture G(D) gives weight D to the other mode.")),
            Paragraph(Text("A GeneratedObserver has a total deterministic update and a normalized nonnegative emission row at every configuration. Its complete finite-word law uses that same update after each generated symbol. The theorem allows any carrier Z, so in particular every finite carrier, and every positive integer period L. Only the B update at the chosen starting configuration is periodic. Nothing restricts the configurations or the emissions after an exit. Forecast zeros remain allowed.")),
            Entry("survival", DescribeRole.Definition, ObserverParameters(All("z", Z, All("n", Nat,
                And(Equal(Surv(Zz,Zero),One), Equal(Surv(Zz,Add(N,One)),
                    Mul(Call("row",O,Zz,Call("B")),Surv(Next,N))))))),
                "survival(O,z,n) is the probability of the all-B generated word of length n."),
            Entry("exitCoefficient", DescribeRole.Definition, ObserverParameters(All("z", Z,
                All("n", Nat, All("t", Bool, And(
                    Equal(Exit(Zz,Zero,True),Call("row",O,Zz,Zero)),
                    Equal(Exit(Zz,Zero,False),Add(Call("row",O,Zz,One),Call("row",O,Zz,D(3)))),
                    Equal(Exit(Zz,Add(N,One),T),Mul(Call("row",O,Zz,Call("B")),Exit(Next,N,T)))))))),
                "This is the probability of n B symbols followed by a first exit in {0} for true or {1,3} for false. All subsequent words are summed over the complete normalized continuation law."),
            Entry("periodic_diameter_obstruction", DescribeRole.Theorem, Statement,
                "The complete generated profile cannot satisfy the two stated distance bounds. The period is an iterate of the total B update, independently of any source-observer recurrent class."),
            Paragraph(Text("At horizon H, coarsen each word to its first-exit time and category, or to its all-B survivor. Induction on H bounds the resulting sum of absolute coefficient differences by the original word sum, for every real linear combination A*F2+C*F4 and every real coefficient E multiplying the generated law. On each exit branch normalization and the absolute-sum inequality suffice; the generated continuation need not equal the source continuation. The survivor coefficient A*a^H+C*b^H-E*survival(O,z,H) remains present.")),
            Paragraph(Text("For the dominant and G(D) endpoints, the finite coarsened distance is D*(1-u^H). The triangle defect at any fixed exit coordinate is nonnegative and is bounded by the total defect of a longer finite partition. The two radius assumptions and the endpoint limit force that fixed coordinate defect to zero. Hence the generated dominant exit coefficient lies between (1-D)*(1-v)*v^n and (1-v)*v^n, and the minority coefficient lies between zero and D*(1-u)*u^n. This limit argument does not assert finite-horizon triangle equality.")),
            Paragraph(Text("The minority exit coefficients cannot all vanish: their finite sum is exactly the generated first-minority-exit event mass, whereas the corresponding G(D) event has mass D*(1-u^H). Its event-gap bound and the limit would give D<=D/2. Thus some minority coefficient is positive. This argument retains every finite survivor and does not assume almost-sure exit of the generated process.")),
            Paragraph(Text("Put gamma=survival(O,z,L). The actual product recursion and periodic update give exitCoefficient(O,z,m*L+n,t)=gamma^m*exitCoefficient(O,z,n,t). The positive dominant lower bound makes gamma positive and forces v^L<=gamma by the existing uniform geometric domination theorem. The positive minority coefficient and its upper bound force gamma<=u^L. Since L>0 and u<v, these inequalities contradict each other. The geometric domination theorem is the original NativePeriodicWordLaw.geometric_rate_bound with no additional source parameter assumptions.")))));

    private static Formula Statement => ObserverParameters(All("p",Real,All("q",Real,All("r",Real,
        All("D",Real,All("z",Z,All("L",Nat,Implies(And(
            Call("admissible",P,Q,R),F.NotEqual(Call("a",P,Q),Call("b",R)),Lt(Zero,LL),
            Equal(Call("iterateAt",Call("Bupdate",O),LL,Zz),Zz),Lt(Zero,DD),Lt(DD,One),
            Le(Call("profileDistance",Call("dominantLaw",P,Q,R),Generated),HalfD),
            Le(Call("profileDistance",Call("orientedMixture",P,Q,R,DD),Generated),HalfD)),
            Call("False")))))))));
    private static DocumentBlock.Describe Entry(string name, DescribeRole role, Formula statement, string note) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ObserverMemory/Prediction/FiveModePeriodicDiameter."+name),
            H(name.Replace('_',' ')),StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(note))),role);
    private static Formula ObserverParameters(Formula b) => All("Z",Call("Type"),All("O",Call("GeneratedObserver",Z),b));
    private static Formula All(string n,Formula d,Formula b) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),d,b);
    private static Formula Call(string n,params Formula[] a) => F.Call(n,a);
    private static Formula Equal(Formula l,Formula r) => F.Equal(l,r);
    private static Formula Le(Formula l,Formula r) => new Formula.Relation(l,FormulaRelationOperator.LessThanOrEqual,r);
    private static Formula Lt(Formula l,Formula r) => new Formula.Relation(l,FormulaRelationOperator.LessThan,r);
    private static Formula Implies(Formula l,Formula r) => new Formula.Logic(l,FormulaLogicOperator.Implies,r);
    private static Formula And(params Formula[] xs) => xs.Aggregate((l,r)=>new Formula.Logic(l,FormulaLogicOperator.And,r));
    private static Formula Add(Formula l,Formula r) => F.Add(l,r);
    private static Formula Mul(Formula l,Formula r) => F.Multiply(l,r);
    private static Formula Surv(Formula z,Formula n) => Call("survival",O,z,n);
    private static Formula Exit(Formula z,Formula n,Formula t) => Call("exitCoefficient",O,z,n,t);
    private static Formula Generated => Call("generatedLaw",Call("update",O),Call("row",O),Zz);
    private static Formula Next => Call("update",O,Zz,Call("B"));
    private static Formula HalfD => new Formula.Fraction(DD,D(2));
    private static Formula Z => F.Id("Z");
    private static Formula O => F.Id("O");
    private static Formula Zz => F.Id("z");
    private static Formula P => F.Id("p");
    private static Formula Q => F.Id("q");
    private static Formula R => F.Id("r");
    private static Formula DD => F.Id("D");
    private static Formula N => F.Id("n");
    private static Formula T => F.Id("t");
    private static Formula LL => F.Id("L");
    private static Formula Zero => D(0);
    private static Formula One => D(1);
    private static Formula True => Call("true");
    private static Formula False => Call("false");
    private static Formula Real => Call("Real");
    private static Formula Nat => Call("Nat");
    private static Formula Bool => Call("Bool");
}
