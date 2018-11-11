package globalinterfaces

type GLOBALGobInterface interface {
	MarshalBinary() ([]byte, error)
	UnmarshalBinary(data []byte) error
}

type GLOBALStringer interface {
	String() string
}
