import shlex
from dataclasses import dataclass, field
from typing import Any, Dict, List, Union


@dataclass
class EventDef:
  name: str
  eid: int
  fields: List[tuple]  # (field_name, field_type)


@dataclass
class Event:
  name: str
  values: Dict[str, Any] = field(default_factory=dict)


class PajeParser:

  def __init__(self):
    self.event_defs: Dict[int, EventDef] = {}
    self.events: List[Event] = []

  def parse(self, filename: str):
    with open(filename, "r", encoding="utf-8") as f:
      lines = f.readlines()

    i = 0
    # Event definitions
    while i < len(lines):
      line = lines[i].strip()
      if not line:
        i += 1
        continue
      if line.startswith("%EventDef"):
        parts = line.split()
        name, eid = parts[1], int(parts[2])
        fields = []
        i += 1
        while not lines[i].strip().startswith("%EndEventDef"):
          field_parts = lines[i].strip().split()
          if field_parts and field_parts[0] == "%":
            fname, ftype = field_parts[1], field_parts[2]
            fields.append((fname, ftype))
          i += 1
        self.event_defs[eid] = EventDef(name, eid, fields)
      elif line[0].isdigit():
        # first numeric event encountered → break
        break
      i += 1

    # Events ---
    while i < len(lines):
      line = line = lines[i].strip()
      if not line or line.startswith("#"):
        i += 1
        continue

      parts = shlex.split(line)  # respects quoted strings
      eid = int(parts[0])

      if eid not in self.event_defs:
        raise Exception(f"Unknown event id {eid}")

      edef = self.event_defs[eid]
      values = {}
      for (fname, ftype), val in zip(edef.fields, parts[1:]):
        values[fname] = self.cast_value(val, ftype)
      self.events.append(Event(edef.name, values))
      i += 1

  def cast_value(self, val: str, ftype: str) -> Union[int, float, str, tuple]:
    if ftype == "int":
      return int(val)
    elif ftype in ("date", "double"):
      return float(val)
    elif ftype == "string":
      return val
    elif ftype == "hex":
      return int(val, 16)
    elif ftype == "color":
      # colors are stored as "r g b"
      return tuple(map(float, val.replace('"', "").split()))
    else:
      return val
