#define ATS_DYNLOADFLAG 0
#define ATS_PACKNAME "vicpack"
#define ATS_EXTERN_PREFIX "vicpack"
#include "share/atspre_staload.hats" // include template definitions

#define LIBS_targetloc "../libs" (* search path for external libs *)
staload BS="{$LIBS}/ats-bytestring/SATS/bytestring.sats"

datavtype Vicpack =
  | driver_info_vt of // 0x01
    @{ is_enabled=bool
    , index=byte
    , slot=byte
    , type=byte
    }
  | internal_battery_on_die_vt of uint32 // 0x07
  | internal_battery_vt of double // 0x08
  | internal_temperature_vt of double // 0x0B
  | charge_vt of sint // 0x13 says, that it is cint16, but formula uses all 4 bytes for calculations
  | temperature_vt of double // 0x14
  | humidity_vt of uint32 // 0x15
  | presure_vt of uint32 // 0x16
  | acceleration_x_vt of double // 0x17
  | acceleration_y_vt of double // 0x18
  | acceleration_z_vt of double // 0x19
  | switch_interrupt_vt of // 0x1A
    @{ button_pressed=bool
     , pin=uint32
     }
  | audio_average_vt of uint32 // 0x1B
  | audio_max_vt of uint32 // 0x1C
  | audio_spl_vt of uint32 // 0x1D
  | ambient_light_visible_vt of double // 0x1E
  | ambient_light_ir_vt of uint32 // 0x1F
  | ambient_light_uv_vt of uint32 // 0x20
  | co2_level_vt of uint32 // 0x21
  | distance_vt of uint32 // 0x22
  | sample_rate_vt of uint32 // 0x23
  | voc_iaq_vt of // 0x2B
    @{ state=byte
     , index=byte
     }
  | voc_temperature_vt of double // 0x2C
  | voc_humidity_vt of double // 0x2D
  | voc_pressure_vt of double // 0x2E
  | voc_ambient_light_vt of double // 0x2F
  | voc_sound_peak_vt of uint16 // 0x30
  | tof_distance_vt of // 0x31
    @{ state=byte
     , distance=uint16
     }
  | accelerometer_status_vt of uint32 // 0x32
  | voltage_vt of double // 0x34
  | voltage_dff_vt of double // 0x35
  | voltage_ref_vt of double // 0x36
  | falling_counter_vt of uint32 // 0x37
  | rising_counter_vt of uint32 // 0x38
  | gps_data_vt of uint32 // 0x51
  | eco2_vt of uint32 // 0x52
  | device_id_vt of uint64 // 0x83
  | device_pin_vt of uint32 // 0x84
  | rssi_level_vt of uint32 // 0x85
  | cell_id_vt of uint64 // 0x86