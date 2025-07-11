import Mathlib.Data.Finset.Basic

variable
  /- we'll usually use α for the node type's labels -/
  {α: Type} [DecidableEq α]
  /- we'll usually use β for the rule name's labels -/
  {β: Type} [DecidableEq β]

structure NodeContext (α : Type) where
  /-- a finite set of all node types for this context -/
  node_types: Finset α
  /-- maps a node type to its arity of positive polarity -/
  pos_ports: node_types → ℕ
  /-- maps a node type to its arity of negative polarity -/
  neg_ports: node_types → ℕ

inductive Polarity where
  | pos : Polarity
  | neg : Polarity
  deriving DecidableEq, Repr

def Polarity.flip : Polarity → Polarity
  | Polarity.pos => Polarity.neg
  | Polarity.neg => Polarity.pos

@[simp]
lemma flip_flip_is_id (pol : Polarity) : pol.flip.flip = pol := by
  cases pol <;> rfl

def port_range
  {ctx: NodeContext α}
  (t : ctx.node_types)
  (port_pol: Polarity) : Type
  := Fin (match port_pol with
    | Polarity.pos => ctx.pos_ports t
    | Polarity.neg => ctx.neg_ports t)

-- TODO: I still would prefer if these defs were inside InteractionNet but :shrug:
/-- dependent product type between a node and a index for one of its positive ports -/
def PosPort
  {ctx: NodeContext α}
  {nodes: Finset ℕ}
  (assign_node_type: nodes → ctx.node_types): Type := (n: nodes) × (Fin (ctx.pos_ports (assign_node_type n)))

/-- dependent product type between a node and a index for one of its negative ports -/
def NegPort
  {ctx: NodeContext α}
  {nodes: Finset ℕ}
  (assign_node_type: nodes → ctx.node_types): Type := (n: nodes) × (Fin (ctx.neg_ports (assign_node_type n)))

/--
  an interaction net is a set of nodes and a wiring between their ports
  (one of the most obvious definitions we'll have)
-/
structure InteractionNet (ctx: NodeContext α) where
  /-- a finite set of indices for all of the net's nodes -/
  nodes: Finset ℕ
  /-- a mapping that associates each node to its respective type -/
  assign_node_type: nodes → ctx.node_types

  wiring: (PosPort assign_node_type) ≃ (NegPort assign_node_type)

-- TODO: maybe we need to move `has_principal_{pos,neg}` to these as well
-- that would suck tho. but I don't think this is necessary to the well-formedness
-- of the rules.
/--
  a disjoint sum of the types of ports to be interpreted as
  boundary ports of positive polarity of the rule. these are:
  1. the non-principal positive ports of the positive node
  2. all the positive ports of the negative node

  these are given as indices, and implicitly the first entry's ports
  should be shifted by 1, as 0 is the principal port and the
  first entry only has boundary non-pricipal ports.
-/
def BoundPos
  {ctx: NodeContext α}
  (pos_node_type: ctx.node_types)
  (neg_node_type: ctx.node_types): Type :=
      (Fin (ctx.pos_ports pos_node_type - 1))
    ⊕ (Fin (ctx.pos_ports neg_node_type))

/--
  a disjoint sum of the types of ports to be interpreted as
  boundary ports of negative polarity of the rule. these are:
  1. the non-principal negative ports of the negative node
  2. all the negative ports of the positive node

  these are given as indices, and implicitly the first entry's ports
  should be shifted by 1, as 0 is the principal port and the
  first entry only has boundary non-pricipal ports.
-/
def BoundNeg
  {ctx: NodeContext α}
  (pos_node_type: ctx.node_types)
  (neg_node_type: ctx.node_types): Type :=
      (Fin (ctx.neg_ports neg_node_type - 1))
    ⊕ (Fin (ctx.neg_ports pos_node_type))

/--
  the ports of output nodes of positive polarity, given as a product of a node's
  index and its positive ports indices.
-/
def OutPos
  {ctx: NodeContext α}
  {output_nodes: Finset ℕ}
  (o: output_nodes → ctx.node_types): Type :=
    (n: output_nodes) × Fin (ctx.pos_ports (o n))

/--
  the output ports of positive polarity, given as a product of a node's
  index and its negative ports indices.
-/
def OutNeg
  {ctx: NodeContext α}
  {output_nodes: Finset ℕ}
  (o: output_nodes → ctx.node_types): Type :=
    (n: output_nodes) × Fin (ctx.neg_ports (o n))

/--
  an interaction rule describes how to patch a net when a given pair of node types
  (with opposite polarity for their principal ports) is interacting.
-/
structure InteractionRule (ctx: NodeContext α) where
  /-- the node type with positive principal port for this rule -/
  pos_node_type: ctx.node_types
  /-- the node type with negative principal port for this rule -/
  neg_node_type: ctx.node_types

  /-- asserts that the positive node type for this rule has a positive principal port (index 0) -/
  has_principal_pos: 0 < ctx.pos_ports pos_node_type
  /-- asserts that the positive node type for this rule has a negative principal port (index 0) -/
  has_principal_neg: 0 < ctx.neg_ports neg_node_type

  /-- a finite set of indices for all output nodes of this rule -/
  output_nodes: Finset ℕ
  /-- a mapping that associates each output node of the rule to its respective type -/
  o: output_nodes → ctx.node_types

  /--
    "a bijection i : B− + O+ → B+ + O− wiring each positive (output or boundary)
    port onto a negative (output or boundary) port.

    notice that negative boundary ports may be wired to negative output ports by i,
    and similarly for positive boundary ports and positive output ports. this is
    because the boundary ports correspond to the ports facing outward on the input,
    and such ports are wired to ports facing the same direction on the output."

    this makes more sense inside of a trace, where we have the concept of trace polarity
    and then input nodes of an interaction will be considered of negative polarity,
    and their ports will have flipped polarities. in that sense, the boundary ports
    are not connecting to ports of same trace polarity, but of opposite ones
  -/
  i:
      (BoundNeg pos_node_type neg_node_type ⊕ OutPos o)
    ≃ (BoundPos pos_node_type neg_node_type ⊕ OutNeg o)

def InteractionRule.Ports
  {ctx: NodeContext α}
  (rule: InteractionRule ctx): Type :=
    (BoundNeg rule.pos_node_type rule.neg_node_type ⊕ OutPos rule.o)
  ⊕ (BoundPos rule.pos_node_type rule.neg_node_type ⊕ OutNeg rule.o)

structure TraceSetting (α β : Type) (ctx: NodeContext α) where
  /-- a finite set of labels for rule names that could appear on the trace -/
  rule_names: Finset β
  /-- a mapping that gets an interaction rule by its name in the setting -/
  rules: rule_names → InteractionRule ctx

/--
  positive nodes come from:
    1. starting net nodes
    2. output nodes from interaction steps
-/
def PosNodes
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  (net_start: InteractionNet ctx)
  (num_steps: ℕ)
  (steps: Fin num_steps → ts.rule_names)
  (t: ctx.node_types) : Type :=
    {n : net_start.nodes // net_start.assign_node_type n = t} ⊕
    (Σ s : Fin num_steps,
      {n : (ts.rules (steps s)).output_nodes // ((ts.rules (steps s)).o n) = t})

/--
  negative nodes come from:
    1. ending net nodes
    2. input nodes consumed by interaction steps
-/
def NegNodes
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  (net_end: InteractionNet ctx)
  (num_steps: ℕ)
  (steps: Fin num_steps → ts.rule_names)
  (t: ctx.node_types) : Type :=
    {n : net_end.nodes // net_end.assign_node_type n = t} ⊕
    {s : Fin num_steps // (ts.rules (steps s)).pos_node_type = t} ⊕
    {s : Fin num_steps // (ts.rules (steps s)).neg_node_type = t}

/--
  (possibly-temporally-inconsistent) interaction trace

  notice the trace is not defined in the obvious (and inefficient way) as a
  list of nets, it's not even obvious this definition could amount to a trace.

  the intuition behind this definition is that interactions are linear, so instead
  of taking a snapshot of the net at each step of the trace, and connecting all of
  that together, we can have a more sparse definition: every node is produced and
  consumed exactly once, so we can omit all the nodes/ports that don't get consumed
  in a step, and just have a mapping between all nodes produced (positive) to all
  nodes consumed (negative) of the same type!

  then the only thing that's missing is a way to wire the nodes/ports produced by an
  interaction to the hole that interaction left in the net (boundary ports), which
  is given by the internal wirings of every step's interaction.
-/
structure InteractionTrace (ctx: NodeContext α) (ts: TraceSetting α β ctx) where
  /-- input interaction net of the trace's first step -/
  net_start: InteractionNet ctx
  /-- output interaction net of the trace's last step -/
  net_end: InteractionNet ctx
  /-- total amount of steps in the trace -/
  num_steps: ℕ
  /-- a mapping of a step number to its corresponding rule name -/
  steps: Fin num_steps → ts.rule_names

  /-- the node bijection for each type -/
  b: ∀ t: ctx.node_types,
    (PosNodes net_start num_steps steps t) ≃ (NegNodes net_end num_steps steps t)

/-- a node's level, used for temporal consistency -/
def node_level
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  (trace: InteractionTrace ctx ts) :
  (Σ t,
    (PosNodes trace.net_start trace.num_steps trace.steps t) ⊕
    (NegNodes trace.net_end trace.num_steps trace.steps t)
  ) → ℕ -- TODO: turn this ℕ into (Fin (trace.num_steps + 1))
  | ⟨_, Sum.inl (Sum.inl _)⟩ => 0                    -- starting net
  | ⟨_, Sum.inl (Sum.inr ⟨s, _⟩)⟩ => s + 1      -- output of step s
  | ⟨_, Sum.inr (Sum.inl _)⟩ => trace.num_steps + 1  -- ending net
  | ⟨_, Sum.inr (Sum.inr (Sum.inl s))⟩ => s.val + 1  -- pos input
  | ⟨_, Sum.inr (Sum.inr (Sum.inr s))⟩ => s.val + 1  -- neg input

/--
  a trace node is a node in a trace (duh)

  technically at each step of a trace we have a different net, but since interactions
  are linear and thus every node/port is consumed exactly once (if you account for the
  end net),
-/
structure TraceNode
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  (trace: InteractionTrace ctx ts) where
  t : ctx.node_types
  node : (PosNodes trace.net_start trace.num_steps trace.steps t) ⊕
         (NegNodes trace.net_end trace.num_steps trace.steps t)

/--
  a trace port is the port of a trace node, lifted.

  it's defined so we can define trace port polarity, which is necessary
  for defining temporal consistency.
-/
structure TracePort
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  (trace: InteractionTrace ctx ts) where
  trace_node : TraceNode trace
  -- port polarity in the node context
  port_pol : Polarity
  port : port_range trace_node.t port_pol

-- the level of a port is the level of its node
def port_level
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  {trace: InteractionTrace ctx ts}
  (trace_port : TracePort trace) : ℕ :=
  node_level trace ⟨trace_port.trace_node.t, trace_port.trace_node.node⟩

/--
  the polarity of a port in the trace, necessary for defining temporal consistency

  the trace polarity of a port will be equal to its node context if it's a port
  from a positive (trace) node, and its opposite if it's a port on a negative (trace) node
-/
def TracePort.trace_polarity
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  {trace: InteractionTrace ctx ts}
  (trace_port : TracePort trace) : Polarity :=
  match trace_port.trace_node.node with
  -- for ports on positive trace nodes,
  -- trace port polarity is the same as port polarity
  | Sum.inl _ => trace_port.port_pol
  -- for ports on negative trace nodes,
  -- trace port polarity is the flipped port polarity
  | Sum.inr _ => trace_port.port_pol.flip

/--
  the bijection b* defined from lifting the bijections b_t (between
  nodes of same type but opposite polarities) to ports

  intuitively b* will map a port from when its introduced
  to when it's consumed. ports and nodes that don't get consumed by an
  interaction and reach the end net on the trace, are consumed then.
-/
def b_star
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  (trace: InteractionTrace ctx ts) :
  TracePort trace → TracePort trace
  | ⟨⟨t, Sum.inl n⟩, pol, port⟩ =>
      ⟨⟨t, Sum.inr (trace.b t n)⟩, pol, port⟩
  | ⟨⟨t, Sum.inr n⟩, pol, port⟩ =>
      ⟨⟨t, Sum.inl ((trace.b t).symm n)⟩, pol, port⟩

def TracePosPort
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  (trace: InteractionTrace ctx ts) : Type :=
  { p : TracePort trace // p.trace_polarity = Polarity.pos }

def TraceNegPort
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  (trace: InteractionTrace ctx ts) : Type :=
  { p : TracePort trace // p.trace_polarity = Polarity.neg }

-- TODO: address later
set_option linter.unusedSectionVars false
lemma b_star_flips_trace_pol
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  {trace: InteractionTrace ctx ts}
  (p : TracePort trace) :
  (b_star trace p).trace_polarity = p.trace_polarity.flip := by
  cases p with
  | mk trace_node port_pol port =>
    cases trace_node with
    | mk t node =>
      cases node <;> simp [b_star, TracePort.trace_polarity, Polarity.flip]
      cases port_pol <;> simp

lemma b_star_involutive
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  {trace: InteractionTrace ctx ts}
  (p : TracePort trace) :
  b_star trace (b_star trace p) = p := by
  cases p with
  | mk trace_node port_pol port =>
    cases trace_node with
    | mk t node =>
      cases node <;> simp [b_star]

def b_star_bij_trace_port_pols
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  (trace: InteractionTrace ctx ts) :
  TracePosPort trace ≃ TraceNegPort trace where
  toFun := fun ⟨p, hp⟩ =>
    ⟨b_star trace p, by simp [b_star_flips_trace_pol, hp, Polarity.flip]⟩
  invFun := fun ⟨p, hp⟩ =>
    ⟨b_star trace p, by simp [b_star_flips_trace_pol, hp, Polarity.flip]⟩
  left_inv := by
    intro ⟨p, hp⟩
    simp [b_star_involutive]
  right_inv := by
    intro ⟨p, hp⟩
    simp [b_star_involutive]

def is_principal_port
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  {trace: InteractionTrace ctx ts}
  (p : TracePort trace) : Bool :=
  p.port.val = 0

def start_port_to_trace_port
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  {trace: InteractionTrace ctx ts}
  -- TODO: this is horrible, I wish there was a neat way to refactor the Pos/NegNode types
  : (PosPort trace.net_start.assign_node_type) ⊕ (NegPort trace.net_start.assign_node_type)
    → TracePort trace
  | Sum.inl ⟨n, p⟩ =>
      let t := trace.net_start.assign_node_type n
      ⟨⟨t, Sum.inl (Sum.inl ⟨n, rfl⟩)⟩, Polarity.pos, p⟩
  | Sum.inr ⟨n, p⟩ =>
      let t := trace.net_start.assign_node_type n
      ⟨⟨t, Sum.inl (Sum.inl ⟨n, rfl⟩)⟩, Polarity.neg, p⟩

def end_port_to_trace_port
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  {trace: InteractionTrace ctx ts}
  : (PosPort trace.net_end.assign_node_type) ⊕ (NegPort trace.net_end.assign_node_type)
    → TracePort trace
  | Sum.inl ⟨n, p⟩ =>
    let t := trace.net_end.assign_node_type n
    ⟨⟨t, Sum.inr (Sum.inl ⟨n, rfl⟩)⟩, Polarity.pos, p⟩
  | Sum.inr ⟨n, p⟩ =>
    let t := trace.net_end.assign_node_type n
    ⟨⟨t, Sum.inr (Sum.inl ⟨n, rfl⟩)⟩, Polarity.neg, p⟩

def output_port_to_rule_port
  {ctx: NodeContext α}
  {rule: InteractionRule ctx}
  (pol: Polarity)
  (n: rule.output_nodes)
  (p: port_range (rule.o n) pol)
  : rule.Ports :=
  match pol with
  | Polarity.pos => Sum.inl (Sum.inr ⟨n, p⟩)
  | Polarity.neg => Sum.inr (Sum.inr ⟨n, p⟩)

def rule_port_to_trace_port
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  {trace: InteractionTrace ctx ts}
  (s: Fin trace.num_steps)
  (port: (ts.rules (trace.steps s)).Ports)
  : TracePort trace :=
  let rule := ts.rules (trace.steps s)
  match port with
  -- BoundNeg: negative boundary port
  | Sum.inl (Sum.inl boundary_neg) =>
    match boundary_neg with
    -- non-principal negative port of negative input (shift by 1)
    | Sum.inl p =>
      ⟨
        ⟨rule.neg_node_type, Sum.inr (Sum.inr (Sum.inr ⟨s, rfl⟩))⟩,
        Polarity.neg,
        ⟨
          p.val + 1,
          by
            have : p.val < ctx.neg_ports rule.neg_node_type - 1 := p.isLt
            simp only
            omega
        ⟩
      ⟩
    -- negative port of positive input
    | Sum.inr p =>
      ⟨
        ⟨rule.pos_node_type, Sum.inr (Sum.inr (Sum.inl ⟨s, rfl⟩))⟩,
        Polarity.neg,
        p
      ⟩
  -- OutPos: positive output port
  | Sum.inl (Sum.inr out_pos) =>
    let ⟨n, p⟩ := out_pos
    ⟨
      ⟨rule.o n, Sum.inl (Sum.inr ⟨s, n, rfl⟩)⟩,
      Polarity.pos,
      p
    ⟩
  -- BoundPos: positive boundary port
  | Sum.inr (Sum.inl boundary_pos) =>
    match boundary_pos with
    -- non-principal positive port of positive input (shift by 1)
    | Sum.inl p =>
      ⟨
        ⟨rule.pos_node_type, Sum.inr (Sum.inr (Sum.inl ⟨s, rfl⟩))⟩,
        Polarity.pos,
        ⟨
          p.val + 1,
          by
            have : p.val < ctx.pos_ports rule.pos_node_type - 1 := p.isLt
            simp
            omega
        ⟩
      ⟩
    -- positive port of negative input
    | Sum.inr p =>
      ⟨
        ⟨rule.neg_node_type, Sum.inr (Sum.inr (Sum.inr ⟨s, rfl⟩))⟩,
        Polarity.pos,
        p
      ⟩
  -- OutNeg: negative output port
  | Sum.inr (Sum.inr out_neg) =>
    let ⟨n, p⟩ := out_neg
    ⟨
      ⟨rule.o n, Sum.inl (Sum.inr ⟨s, n, rfl⟩)⟩,
      Polarity.neg,
      p
    ⟩

-- r_star follows wirings within each level
def r_star
  {ctx: NodeContext α}
  {ts: TraceSetting α β ctx}
  (trace: InteractionTrace ctx ts)
  : TracePort trace → TracePort trace

  -- starting net, positive port
  | ⟨⟨t, Sum.inl (Sum.inl n)⟩, Polarity.pos, port⟩ =>
    let wired := trace.net_start.wiring ⟨n, n.property.symm ▸ port⟩
    start_port_to_trace_port (Sum.inr wired)

  -- starting net, negative port
  | ⟨⟨t, Sum.inl (Sum.inl n)⟩, Polarity.neg, port⟩ =>
    let wired := trace.net_start.wiring.symm ⟨n, n.property.symm ▸ port⟩
    start_port_to_trace_port (Sum.inl wired)

  -- ending net, positive port
  | ⟨⟨t, Sum.inr (Sum.inl n)⟩, Polarity.pos, port⟩ =>
    let wired := trace.net_end.wiring ⟨n, n.property.symm ▸ port⟩
    end_port_to_trace_port (Sum.inr wired)

  -- ending net, negative port
  | ⟨⟨t, Sum.inr (Sum.inl n)⟩, Polarity.neg, port⟩ =>
    let wired := trace.net_end.wiring.symm ⟨n, n.property.symm ▸ port⟩
    end_port_to_trace_port (Sum.inl wired)

  -- output nodes from steps
  | ⟨⟨t, Sum.inl (Sum.inr ⟨s, output_node⟩)⟩, pol, port⟩ =>
    let rule := ts.rules (trace.steps s)
    let rule_port := output_port_to_rule_port pol output_node.val (output_node.property.symm ▸ port)
    match rule_port with
    | Sum.inl p =>
      let wired := rule.i p
      rule_port_to_trace_port s (Sum.inr wired)
    | Sum.inr p =>
      let wired := rule.i.symm p
      rule_port_to_trace_port s (Sum.inl wired)

  -- positive input node, positive port
  | ⟨⟨t, Sum.inr (Sum.inr (Sum.inl s))⟩, Polarity.pos, port⟩ =>
    let rule := ts.rules (trace.steps s)
    if h : port.val = 0 then
      -- principal port
      ⟨
        ⟨rule.neg_node_type, Sum.inr (Sum.inr (Sum.inr ⟨s, rfl⟩))⟩,
        Polarity.neg,
        ⟨0, rule.has_principal_neg⟩
      ⟩
    else
      -- non-principal port
      let boundary_port : BoundPos rule.pos_node_type rule.neg_node_type :=
        Sum.inl ⟨
          port.val - 1,
          by
            simp at port
            have isLt : port.val < ctx.pos_ports t := port.isLt
            have : t = rule.pos_node_type := s.property.symm
            simp only [this] at isLt
            omega
        ⟩
      -- let rule_port : rule.Ports := Sum.inr (Sum.inl boundary_port)
      let wired := rule.i.symm (Sum.inl boundary_port)
      rule_port_to_trace_port s (Sum.inl wired)

  -- positive input node, negative port
  | ⟨⟨t, Sum.inr (Sum.inr (Sum.inl s))⟩, Polarity.neg, port⟩ =>
    let step := s.val
    let rule := ts.rules (trace.steps step)
    -- all negative ports of positive input are boundary (no principal to exclude)
    let boundary_port : BoundNeg rule.pos_node_type rule.neg_node_type :=
      Sum.inr (s.property.symm ▸ port)
    let wired := rule.i (Sum.inl boundary_port)
    rule_port_to_trace_port step (Sum.inr wired)

  -- negative input node, positive port
  | ⟨⟨t, Sum.inr (Sum.inr (Sum.inr s))⟩, Polarity.pos, port⟩ =>
    let step := s.val
    let rule := ts.rules (trace.steps step)

    -- all positive ports of negative input are boundary
    let boundary_port : BoundPos rule.pos_node_type rule.neg_node_type :=
      Sum.inr (s.property.symm ▸ port)
    let wired := rule.i.symm (Sum.inl boundary_port)
    rule_port_to_trace_port step (Sum.inl wired)

  -- negative input node, negative port
  | ⟨⟨t, Sum.inr (Sum.inr (Sum.inr s))⟩, Polarity.neg, port⟩ =>
    let step := s.val
    let rule := ts.rules (trace.steps step)

    if h : port.val = 0 then
      -- principal negative connects to principal positive
      ⟨⟨rule.pos_node_type, Sum.inr (Sum.inr (Sum.inl ⟨step, rfl⟩))⟩,
        Polarity.pos, ⟨0, rule.has_principal_pos⟩⟩
    else
      -- non-principal negative port → BoundNeg (first case)
      let boundary_port : BoundNeg rule.pos_node_type rule.neg_node_type :=
        Sum.inl ⟨
          port.val - 1,
          by
            have isLt : port.val < ctx.neg_ports t := port.isLt
            have : t = rule.neg_node_type := s.property.symm
            simp only [this] at isLt
            omega
        ⟩
      let wired := rule.i (Sum.inl boundary_port)
      rule_port_to_trace_port step (Sum.inr wired)

lemma net_wiring_involutive
  {ctx: NodeContext α}
  (net : InteractionNet ctx) :
  ∀ p : PosPort net.assign_node_type,
    net.wiring.symm (net.wiring p) = p := fun _p => Equiv.symm_apply_apply _ _

-- proving r* is injective is going to be a fucking ride...
