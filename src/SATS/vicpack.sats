#define ATS_PACKNAME "vicpack"
#define ATS_EXTERN_PREFIX "vicpack"
#include "share/atspre_staload.hats" // include template definitions

#define LIBS_targetloc "../libs" (* search path for external libs *)
staload BS="{$LIBS}/ats-bytestring/SATS/bytestring.sats"

datavtype Vicpack =
  | driver_info_vt of ()// 0x01
(*
    @{ is_enabled=bool
    , index=uchar
    , slot=uchar
    , type=uchar
    }
*)
  | internal_battery_on_die_vt of uint32 // 0x07
  | internal_battery_vt of double // 0x08
//  | internal_temperature_vt of double // 0x0B
//  | charge_vt of sint // 0x13 says, that it is cint16, but formula uses all 4 uchars for calculations
  | temperature_vt of double // 0x14
  | humidity_vt of uint32 // 0x15
//  | presure_vt of uint32 // 0x16
//  | acceleration_x_vt of double // 0x17
//  | acceleration_y_vt of double // 0x18
//  | acceleration_z_vt of double // 0x19
//  | switch_interrupt_vt of // 0x1A
//    @{ button_pressed=bool
//     , pin=uint32
//     }
//  | audio_average_vt of uint32 // 0x1B
//  | audio_max_vt of uint32 // 0x1C
//  | audio_spl_vt of uint32 // 0x1D
//  | ambient_light_visible_vt of double // 0x1E
//  | ambient_light_ir_vt of uint32 // 0x1F
//  | ambient_light_uv_vt of uint32 // 0x20
  | co2_level_vt of uint32 // 0x21
//  | distance_vt of uint32 // 0x22
//  | sample_rate_vt of uint32 // 0x23
  | voc_iaq_vt of // 0x2B
    @{ state=uchar
     , index=uint16
     }
  | voc_temperature_vt of double // 0x2C
  | voc_humidity_vt of double // 0x2D
  | voc_pressure_vt of double // 0x2E
  | voc_ambient_light_vt of double // 0x2F
  | voc_sound_peak_vt of uint16 // 0x30
(*
  | tof_distance_vt of // 0x31
    @{ state=uchar
     , distance=uint16
     }
*)
//  | accelerometer_status_vt of uint32 // 0x32
//  | voltage_vt of double // 0x34
//  | voltage_dff_vt of double // 0x35
//  | voltage_ref_vt of double // 0x36
//  | falling_counter_vt of uint32 // 0x37
//  | rising_counter_vt of uint32 // 0x38
//  | gps_data_vt of uint32 // 0x51
(*
  | eco2_and_pir_vt of // 0x52
    @{ eTVOC = uint32
     , eCO2 = uint32
     , PIR_Present = bool
     , eCO2_Status = uint8
     , eCO2_Error = uint8
     , Audio_level = double
     , ambient_light = double
     }
*)
  | evoc_eco2_vt of // 0x54
    @{ Static_IAQ = uint16
     , eCO2 = uint16
     , IQA = uint16
     , IQA_State = uint16
     , voc_temperature = float
     , voc_humidity = float
     , voc_pressure = float
     , ambient_light = uint16
     , noise_level = float
     }
//  | device_id_vt of uint64 // 0x83
//  | device_pin_vt of uint32 // 0x84
//  | rssi_level_vt of uint32 // 0x85
//  | cell_id_vt of uint64 // 0x86

fn
  parse
  {len,offset,cap,ucap,refcnt: nat | len >= 6}{dynamic:bool}{l:addr}
  ( i: &($BS.Bytestring_vtype(len, offset, cap, ucap, refcnt, dynamic, l)) >> _
  ):
  ( List0_vt( Vicpack)
  , size_t (* how many packages haven't been decoded due to errors or missing support *)
  )

fn
  parse_package
  {len,offset, cap, ucap, refcnt: nat | len >= 5; len == (len / 5) * 5}{dynamic:bool}{l:agz}
  ( i: &$BS.Bytestring_vtype(len, offset, cap, ucap, refcnt, dynamic, l) >> $BS.Bytestring_vtype( olen, ooffset, cap, ucap, refcnt, dynamic, l)
  ):
  #[olen,ooffset:nat | olen == (olen / 5) * 5; olen < len]
  Option_vt( Vicpack)
  

fn
  free_vicpack
  ( i: Vicpack
  ):<!wrt>
  void

overload free with free_vicpack

fn
  print_vicpack
  ( i: !Vicpack): void

(* provides a list of key-values pairs from given Vicpack package, where key is a name of value*)
fn
  package2kvs
  ( i: !Vicpack
  ):
  [n: nat]
  list_vt( @($BS.BytestringNSH1, $BS.BytestringNSH1), n)